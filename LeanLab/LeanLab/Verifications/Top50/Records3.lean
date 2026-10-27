/-
OEIS A025018 and A025019, the records of the least Goldbach prime, rows 47 to 69: `minGB n = p` for each row, zero sorry.
Divisors and Pratt certificates found by Python, checked by the Lean kernel.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base

namespace LeanLab.Verifications.Top50.Records3

open LeanLab.Verifications LeanLab.Verifications.Top50
open LeanLab.Verifications.Pratt (pB)

theorem p57417161 : Nat.Prime 57417161 := by
  refine Pratt.pratt 57417161 3 [(2, 3), (5, 1), (17, 1), (84437, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1033508899 : Nat.Prime 1033508899 := by
  refine Pratt.pratt 1033508899 3 [(2, 1), (3, 2), (57417161, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p57417161

theorem p80613694123 : Nat.Prime 80613694123 := by
  refine Pratt.pratt 80613694123 5 [(2, 1), (3, 1), (13, 1), (1033508899, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1033508899

theorem p5320503812119 : Nat.Prime 5320503812119 := by
  refine Pratt.pratt 5320503812119 3 [(2, 1), (3, 1), (11, 1), (80613694123, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p80613694123

theorem p8342945540519 : Nat.Prime 8342945540519 := by
  refine Pratt.pratt 8342945540519 7 [(2, 1), (41, 1), (235441, 1), (432139, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p10591605896479 : Nat.Prime 10591605896479 := by
  refine Pratt.pratt 10591605896479 3 [(2, 1), (3, 1), (31, 1), (99131, 1), (574433, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p33287872291 : Nat.Prime 33287872291 := by
  refine Pratt.pratt 33287872291 3 [(2, 1), (3, 1), (5, 1), (137, 1), (331, 1), (24469, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p12982270193491 : Nat.Prime 12982270193491 := by
  refine Pratt.pratt 12982270193491 2 [(2, 1), (3, 1), (5, 1), (13, 1), (33287872291, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p33287872291

theorem p15197900990161 : Nat.Prime 15197900990161 := by
  refine Pratt.pratt 15197900990161 17 [(2, 4), (3, 1), (5, 1), (7, 1), (23, 1), (13597, 1), (28927, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p28998050645719 : Nat.Prime 28998050645719 := by
  refine Pratt.pratt 28998050645719 6 [(2, 1), (3, 2), (7, 1), (11, 1), (61, 1), (11353, 1), (30211, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p46878442761763 : Nat.Prime 46878442761763 := by
  refine Pratt.pratt 46878442761763 2 [(2, 1), (3, 3), (59, 1), (19687, 1), (747391, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p4538690657 : Nat.Prime 4538690657 := by
  refine Pratt.pratt 4538690657 3 [(2, 5), (31, 1), (271, 1), (16883, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p76903574492209 : Nat.Prime 76903574492209 := by
  refine Pratt.pratt 76903574492209 7 [(2, 4), (3, 1), (353, 1), (4538690657, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4538690657

theorem p184162477855171 : Nat.Prime 184162477855171 := by
  refine Pratt.pratt 184162477855171 2 [(2, 1), (3, 1), (5, 1), (71, 1), (1499, 1), (1579, 1), (36529, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p69709853 : Nat.Prime 69709853 := by
  refine Pratt.pratt 69709853 2 [(2, 2), (29, 1), (600947, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p217361316701359 : Nat.Prime 217361316701359 := by
  refine Pratt.pratt 217361316701359 17 [(2, 1), (3, 2), (311, 1), (557, 1), (69709853, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p69709853

theorem p4062135695983 : Nat.Prime 4062135695983 := by
  refine Pratt.pratt 4062135695983 12 [(2, 1), (3, 1), (7, 1), (13, 1), (19, 1), (9241, 1), (42373, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p389965026814369 : Nat.Prime 389965026814369 := by
  refine Pratt.pratt 389965026814369 7 [(2, 5), (3, 1), (4062135695983, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4062135695983

theorem p58535881 : Nat.Prime 58535881 := by
  refine Pratt.pratt 58535881 11 [(2, 3), (3, 1), (5, 1), (13, 1), (157, 1), (239, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p936574097 : Nat.Prime 936574097 := by
  refine Pratt.pratt 936574097 3 [(2, 4), (58535881, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p58535881

theorem p5619444583 : Nat.Prime 5619444583 := by
  refine Pratt.pratt 5619444583 3 [(2, 1), (3, 1), (936574097, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p936574097

theorem p1047610575830359 : Nat.Prime 1047610575830359 := by
  refine Pratt.pratt 1047610575830359 3 [(2, 1), (3, 2), (10357, 1), (5619444583, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5619444583

theorem p3817620479807 : Nat.Prime 3817620479807 := by
  refine Pratt.pratt 3817620479807 7 [(2, 1), (7, 1), (19, 1), (23, 1), (127, 1), (179, 1), (27449, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p6253262345923867 : Nat.Prime 6253262345923867 := by
  refine Pratt.pratt 6253262345923867 17 [(2, 1), (3, 2), (7, 1), (13, 1), (3817620479807, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p3817620479807

theorem p224942477 : Nat.Prime 224942477 := by
  refine Pratt.pratt 224942477 2 [(2, 2), (11, 1), (5112329, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p24925556008167707 : Nat.Prime 24925556008167707 := by
  refine Pratt.pratt 24925556008167707 2 [(2, 1), (971, 1), (57059, 1), (224942477, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p224942477

theorem p149640373 : Nat.Prime 149640373 := by
  refine Pratt.pratt 149640373 5 [(2, 2), (3, 6), (7, 1), (7331, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p31284177910521169 : Nat.Prime 31284177910521169 := by
  refine Pratt.pratt 31284177910521169 11 [(2, 4), (3, 1), (4355467, 1), (149640373, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p149640373

theorem p51300857 : Nat.Prime 51300857 := by
  refine Pratt.pratt 51300857 3 [(2, 3), (23, 1), (278809, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p5540492557 : Nat.Prime 5540492557 := by
  refine Pratt.pratt 5540492557 2 [(2, 2), (3, 3), (51300857, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p51300857

theorem p10305316156021 : Nat.Prime 10305316156021 := by
  refine Pratt.pratt 10305316156021 6 [(2, 2), (3, 1), (5, 1), (31, 1), (5540492557, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5540492557

theorem p121005022303998583 : Nat.Prime 121005022303998583 := by
  refine Pratt.pratt 121005022303998583 3 [(2, 1), (3, 1), (19, 1), (103, 1), (10305316156021, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p10305316156021

theorem p2748311447177 : Nat.Prime 2748311447177 := by
  refine Pratt.pratt 2748311447177 3 [(2, 3), (19, 1), (131, 1), (5209, 1), (26497, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p16489868683063 : Nat.Prime 16489868683063 := by
  refine Pratt.pratt 16489868683063 3 [(2, 1), (3, 1), (2748311447177, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2748311447177

theorem p255329126688547493 : Nat.Prime 255329126688547493 := by
  refine Pratt.pratt 255329126688547493 2 [(2, 2), (7, 2), (79, 1), (16489868683063, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p16489868683063

theorem p39589817 : Nat.Prime 39589817 := by
  refine Pratt.pratt 39589817 3 [(2, 3), (7, 1), (706961, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p36999059375521 : Nat.Prime 36999059375521 := by
  refine Pratt.pratt 36999059375521 7 [(2, 5), (3, 2), (5, 1), (11, 1), (59, 1), (39589817, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p39589817

theorem p258549426916140749 : Nat.Prime 258549426916140749 := by
  refine Pratt.pratt 258549426916140749 2 [(2, 2), (1747, 1), (36999059375521, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p36999059375521

theorem p2475808594421 : Nat.Prime 2475808594421 := by
  refine Pratt.pratt 2475808594421 2 [(2, 2), (5, 1), (7, 1), (89923, 1), (196661, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p555274351556741881 : Nat.Prime 555274351556741881 := by
  refine Pratt.pratt 555274351556741881 19 [(2, 3), (3, 2), (5, 1), (7, 1), (89, 1), (2475808594421, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2475808594421

theorem p496430231951 : Nat.Prime 496430231951 := by
  refine Pratt.pratt 496430231951 22 [(2, 1), (5, 2), (17, 1), (31, 1), (53, 1), (373, 1), (953, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p887123803077828707 : Nat.Prime 887123803077828707 := by
  refine Pratt.pratt 887123803077828707 2 [(2, 1), (13, 2), (17, 1), (311, 1), (496430231951, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p496430231951

theorem p1757864099 : Nat.Prime 1757864099 := by
  refine Pratt.pratt 1757864099 2 [(2, 1), (89, 1), (2699, 1), (3659, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p3515728199 : Nat.Prime 3515728199 := by
  refine Pratt.pratt 3515728199 7 [(2, 1), (1757864099, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p1757864099

theorem p50056938097363 : Nat.Prime 50056938097363 := by
  refine Pratt.pratt 50056938097363 3 [(2, 1), (3, 2), (7, 1), (113, 1), (3515728199, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p3515728199

theorem p906030579562270301 : Nat.Prime 906030579562270301 := by
  refine Pratt.pratt 906030579562270301 2 [(2, 2), (5, 2), (181, 1), (50056938097363, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p50056938097363

theorem p7069351453 : Nat.Prime 7069351453 := by
  refine Pratt.pratt 7069351453 2 [(2, 2), (3, 1), (193, 1), (3052397, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p2795935116574460009 : Nat.Prime 2795935116574460009 := by
  refine Pratt.pratt 2795935116574460009 3 [(2, 3), (5261, 1), (9397, 1), (7069351453, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p7069351453

theorem p288128372339 : Nat.Prime 288128372339 := by
  refine Pratt.pratt 288128372339 2 [(2, 1), (89, 1), (163, 1), (9930667, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p3325581707333950747 : Nat.Prime 3325581707333950747 := by
  refine Pratt.pratt 3325581707333950747 2 [(2, 1), (3, 5), (11, 1), (17, 1), (127, 1), (288128372339, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p288128372339

def ds_3769 : List ℕ := [
    2, 5, 3, 31, 3, 5, 3, 11, 3, 3, 631, 7,
    3, 5, 3, 3, 3, 227, 9803, 3, 5, 7, 3, 3,
    41, 3, 5, 3, 508019, 3, 19, 3, 3, 59243, 3, 11,
    13, 5, 3, 3, 3, 693877, 3, 5, 3, 389, 2371, 5,
    3, 587, 3, 3, 19, 3, 3, 3, 3, 438527, 17, 3,
    5, 3, 761, 3, 5, 3, 7, 149, 3, 11, 3, 3,
    929, 5, 17, 3, 3, 2851, 3, 53, 3, 15667, 3, 5,
    35381, 3, 3, 7, 3, 5, 3, 3, 137, 3, 7, 3,
    3, 3, 5, 7, 11, 3, 3, 3, 5441, 1319609, 3, 3,
    3, 29, 37, 5, 3, 5641, 1663, 3, 5, 3, 3, 3,
    2957, 5, 3, 3, 536227, 3, 7, 3, 53, 5, 173, 3,
    7, 18289, 3, 317, 3, 17, 3, 3, 11, 3, 5, 3,
    37, 3, 5, 3, 13, 3, 7, 3, 5, 3, 574969, 3,
    7, 3, 13, 3, 3, 3, 97, 3, 3, 3, 17, 1748911,
    11, 3, 3, 1171, 3, 5, 19, 3, 23, 3, 5, 78691,
    7, 3, 5, 3, 3, 3, 89, 5, 7, 3, 5, 3,
    7, 3, 3, 3, 79, 5, 3, 3, 3, 149, 4219, 13,
    3, 3, 887, 3, 3, 2953, 7, 3, 5, 3, 3, 2591,
    13, 3, 3, 3, 7, 17, 3, 5, 3, 479, 3, 3,
    269, 3, 5, 910361, 11, 3, 5, 3, 47, 3, 3, 3,
    3, 4597, 5, 7, 3, 3, 212461, 3, 59, 3, 107, 3,
    3, 19, 3, 3, 127, 1476463, 3, 2969, 5, 3, 11, 5,
    3, 73, 3, 3, 5, 3, 23, 433, 5, 7, 173, 5,
    3, 367, 7, 3, 3, 1093, 3, 71, 11, 3, 5, 3,
    23, 3, 3, 3, 3, 3, 5, 3, 13, 3, 3, 457,
    5, 3, 11, 3, 7, 23, 3, 13, 3, 5, 3, 3,
    3, 5, 3, 103, 3, 3, 5, 3, 11, 7, 3, 5,
    3, 37, 7, 5, 3, 3, 7, 3, 31, 3, 109, 3,
    191, 3, 907, 59, 5, 3, 3, 41, 3, 3, 13, 7,
    3, 3, 150583, 2917, 3, 5, 7, 3, 3, 3, 3, 3,
    61, 3, 3, 3, 5081, 5, 3, 5, 17, 3, 278807, 3,
    3, 9551, 7, 3, 3, 5, 3, 47, 3, 3, 151, 3,
    11, 3, 43, 773, 5, 3, 29, 3, 3, 23, 3, 5,
    89, 3, 13, 3, 19, 3, 7, 3, 3, 11, 31, 3,
    5, 3, 5, 3, 3, 7, 11, 3, 3, 13, 3, 3,
    3, 15559, 3, 3, 5, 3, 3, 3, 193, 3, 114259, 3,
    7, 3, 29, 3, 37, 7, 7321, 276763, 3, 3, 19001, 3,
    11, 3, 5, 3, 31, 47, 7, 3, 3, 3, 101, 3,
    7, 3, 5, 3, 23, 7, 3, 229, 2897, 5, 11, 3,
    3, 1013, 5, 3, 3, 48271, 3, 5, 3, 263, 3, 3,
    5, 3, 3413, 3, 5, 3, 294809, 3, 131, 13, 11, 3,
    3967, 3, 3, 17, 19, 3, 29, 79, 3, 5, 3, 7,
    5, 3, 3, 12613, 1399, 5, 3, 3, 5, 3, 7, 1091,
    3, 439, 3, 31, 5, 1193, 3, 3]

theorem prime_sub_3769 : Nat.Prime (5320503815888 - 3769) := by
  show Nat.Prime 5320503812119
  exact p5320503812119

theorem check_3769 : allC 5320503815888 3769 P10k ds_3769 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 5320503815888 is 3769. -/
theorem minGB_3769 : minGB 5320503815888 = 3769 :=
  minGB_eq_of P10k P10k_complete 5320503815888 3769 (by norm_num) (by norm_num) prime_sub_3769 ds_3769 check_3769

def ds_3917 : List ℕ := [
    2, 149, 95311, 3, 5, 3, 1775869, 3, 41, 2903, 3, 3,
    5, 3, 369071, 71, 23, 3, 3, 5, 3, 3, 7, 34607,
    3, 5, 3, 11, 3, 13, 3, 5, 37123, 3, 14321, 3,
    3, 3, 7, 11, 1091, 3, 5, 3, 23, 3, 3, 3,
    103, 3, 43189, 11, 3, 5, 59, 449, 13, 3, 3, 5,
    3, 7, 3, 5, 3, 251, 3, 3, 13, 3, 19, 18691,
    3, 3, 3, 73, 17, 3, 5, 3, 7, 3, 5, 3,
    3, 2027099, 1223, 3, 5, 3, 19, 71, 3, 5, 3, 7,
    101, 5, 3, 3, 3, 31, 137, 11, 3, 3, 7, 17,
    149, 3, 3, 3, 61, 3, 3, 5, 3, 37, 106219, 13,
    3, 3, 29, 499, 3, 5, 3, 317, 3, 3, 3, 31,
    3, 3, 5, 3, 197, 3, 7, 19, 3, 5, 3, 184969,
    3, 7, 3, 139, 3, 1040387, 3, 5, 3, 23, 3, 5,
    3, 31, 3, 5, 16127, 113, 3, 5, 179, 61, 3, 3,
    3, 271, 373, 3, 5, 3, 3, 7, 3, 5, 3, 3,
    3, 5, 3, 11, 17, 421, 3, 3, 3, 5, 3, 11,
    3, 5, 115807, 269, 3, 3, 7, 1591127, 11, 3, 3, 3,
    7, 8377, 3, 13, 1583, 3, 3, 5, 3, 17, 59, 3,
    3, 5, 131, 29, 3, 3, 17, 3, 7, 3, 229, 13,
    3, 5, 3, 3, 3, 5, 3, 31, 3, 11, 41, 5,
    130367, 3, 3, 3, 7, 11, 3, 5, 3, 604361, 3, 5,
    19, 3, 17, 1193, 3, 3, 7, 3, 3, 178183, 3, 3,
    73, 3, 797, 5, 3, 5857, 3, 3, 3, 3, 3, 3,
    8231, 3, 3, 5, 11, 3, 7, 3, 3, 5, 3, 1303,
    3, 7, 5, 13, 43, 5, 3, 19, 3, 7, 37, 3,
    3, 89, 3, 151, 3, 3, 59, 3, 1990319, 3, 13, 29,
    5, 3, 11, 3, 7, 5, 3, 23, 3, 3, 5, 3,
    11, 3, 3, 3, 137, 191, 3, 41, 3, 29, 3, 7,
    3, 79, 3, 3, 3, 13, 7, 3, 35533, 257, 3, 3,
    5, 167, 3, 3, 5, 3, 3, 7, 193, 5, 11, 37,
    3, 5, 61, 95083, 3, 3, 7, 3, 3, 5, 3, 23,
    11, 3, 3, 313, 5, 3, 13, 3, 5, 17, 3, 677,
    3, 27767, 3, 3, 3, 7, 3, 1597, 103, 3, 5, 3,
    3, 7, 3, 5, 3, 67, 3, 139871, 31, 3, 3, 5,
    3, 23, 3, 17, 13, 3, 3, 5, 11, 3, 7, 127,
    151, 3, 239, 7, 3, 23, 859, 40429, 3, 13, 3, 5,
    3, 7, 3, 5, 3, 3, 3, 3, 97, 19, 3, 1951,
    3, 107, 3, 2111, 3, 3, 3, 5, 19, 11, 3, 5,
    3, 5, 3, 373, 3, 3, 2140013, 3, 3, 3, 3, 4567,
    251, 3, 3, 17, 7, 3, 5, 3, 13, 3, 11, 1451,
    3, 17, 3, 5, 3, 13, 3, 5, 3, 3, 3, 7,
    3, 31, 11, 3, 3, 67, 3, 3, 5, 3, 2146489, 3,
    3, 91393, 13, 3, 3, 3, 19, 5, 3, 499, 3, 3,
    5, 3, 31, 3, 3, 3, 5, 14593, 3, 7, 3, 59,
    11, 5, 3, 605369, 3, 5, 3, 7, 3, 5, 3, 3,
    5]

theorem prime_sub_3917 : Nat.Prime (8342945544436 - 3917) := by
  show Nat.Prime 8342945540519
  exact p8342945540519

theorem check_3917 : allC 8342945544436 3917 P10k ds_3917 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 8342945544436 is 3917. -/
theorem minGB_3917 : minGB 8342945544436 = 3917 :=
  minGB_eq_of P10k P10k_complete 8342945544436 3917 (by norm_num) (by norm_num) prime_sub_3917 ds_3917 check_3917

def ds_4003 : List ℕ := [
    2, 97, 3, 5, 3, 11, 3, 7, 3, 3, 17, 5,
    3, 53, 3, 3, 3, 7, 5, 3, 1458881, 11, 3, 3,
    5, 3, 7, 3, 37, 3, 5, 3, 3, 13, 3, 2707,
    5, 251, 3, 3, 3, 137, 3, 173, 3, 1982957, 11, 3631,
    3, 7, 3, 3, 8597, 3, 3, 3, 3, 7, 5, 3,
    20269, 3, 5, 3, 7, 3, 37, 5, 3, 3137, 3, 3,
    5, 13, 107, 3, 3, 5, 3, 11, 3, 41, 3, 101,
    7, 3, 3, 5, 3, 7901, 3, 3, 5, 3, 67, 3,
    3, 3, 7, 11, 5, 3, 3, 3, 43, 5, 3, 3,
    3, 19, 5, 1033, 3, 1621, 10939, 3, 17, 3, 3, 3,
    29, 11, 3, 3, 7, 3, 167, 3, 5, 7, 11, 3,
    283, 5, 3, 768563, 3, 5, 3, 3, 31, 3, 23, 3,
    19, 3, 89, 3, 7, 3, 5, 3, 59, 3, 5, 3,
    13, 3, 5, 3, 3, 3, 5, 3, 3, 3, 967, 5,
    29, 3, 3, 107, 3, 525001, 101, 3, 17, 3, 509, 7,
    5, 3, 13913, 3, 3, 3, 5, 2700391, 4801, 3, 7, 3,
    19, 3, 3, 3, 11, 1427, 3, 3, 3, 13, 5, 433,
    3, 3, 7, 3, 3, 2213, 5, 3, 67, 3, 3, 7,
    5, 3, 3, 3, 1283, 11, 3, 6827, 3, 3529, 3, 3,
    5, 3, 416503, 17, 457, 3, 103, 3, 7, 3, 3, 3,
    3, 7, 13, 599537, 3, 3, 5, 3, 8731, 3, 5, 3,
    3, 151, 3, 3, 13, 5, 3, 5, 11, 3, 251, 113,
    3, 7, 3, 3, 163, 3, 7, 5, 307, 738107, 5, 7,
    3, 23, 1250479, 3, 3, 7393, 3, 11, 5, 3, 4363, 3,
    29, 3, 3, 3, 3, 3, 13, 3, 7, 3, 3, 5,
    7, 3, 47, 3, 13, 5, 3, 3613, 3, 29, 3, 3,
    3, 19, 3, 13, 3, 3, 31, 3, 389, 5, 3, 41,
    3, 7, 2081, 7, 3, 3, 73, 3, 2340869, 3, 101, 3,
    53, 3, 47, 5, 1451, 3, 3, 19, 3, 3, 23, 5,
    3, 3, 7, 5, 3, 4217, 11, 3, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 27943, 3, 10937, 11, 3, 7, 3,
    3, 37, 5, 3, 3, 131, 3, 5, 3, 3, 5, 3,
    73, 3, 31, 5, 17, 3, 1790309, 3, 3, 5, 3, 13,
    11, 3, 179, 3, 7, 3, 5, 3, 3, 7, 5, 3,
    157, 3, 7, 3, 3, 11, 5, 3, 3, 5, 3, 3,
    3, 5, 3, 3, 187027, 3, 3, 3, 149, 3, 7, 3,
    109, 3, 5, 3, 11, 71, 5, 1013, 3, 3, 19, 3,
    71987, 3, 743, 3, 7, 11, 5, 3, 3, 3, 5, 3,
    31, 3, 7, 3, 13, 29, 3, 97, 5, 11, 199, 3,
    3, 787, 14767, 3, 3, 59, 3, 41, 3, 1786867, 3, 3,
    83, 3, 5, 3, 7, 3, 137, 3, 17, 11, 5, 3,
    683, 3, 3, 53, 5, 3, 1962809, 13, 3, 23, 3, 5,
    947, 3, 3, 7, 5, 11, 3, 3, 7, 3, 47, 5,
    3, 11, 3, 5, 2089, 2621, 3, 3, 281791, 3, 19, 3,
    3, 3, 569, 3, 5, 3, 127, 3, 5, 3, 2389799, 5,
    3, 3, 1567, 3, 3, 83, 3323, 3, 5, 3, 3]

theorem prime_sub_4003 : Nat.Prime (10591605900482 - 4003) := by
  show Nat.Prime 10591605896479
  exact p10591605896479

theorem check_4003 : allC 10591605900482 4003 P10k ds_4003 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 10591605900482 is 4003. -/
theorem minGB_4003 : minGB 10591605900482 = 4003 :=
  minGB_eq_of P10k P10k_complete 10591605900482 4003 (by norm_num) (by norm_num) prime_sub_4003 ds_4003 check_4003

def ds_4027 : List ℕ := [
    2, 5, 3, 263, 3, 5, 3, 173, 3, 3, 751, 13,
    3, 5, 3, 3, 3, 11, 4919, 3, 5, 97, 3, 3,
    7, 3, 5, 3, 19, 3, 11, 3, 3, 7, 3, 1031,
    41, 5, 3, 3, 3, 7, 3, 5, 3, 42853, 563, 5,
    3, 299329, 3, 3, 17, 3, 3, 3, 3, 13, 37, 3,
    5, 3, 7, 3, 5, 3, 691, 19, 3, 7, 3, 3,
    47, 5, 79, 3, 3, 199, 3, 223, 3, 1237, 3, 5,
    127, 3, 3, 11, 3, 5, 3, 3, 4027, 3, 37, 3,
    3, 3, 5, 193, 17, 3, 3, 3, 580373, 277, 3, 3,
    3, 7, 329347, 5, 3, 43, 31, 3, 5, 3, 3, 3,
    13, 5, 3, 3, 78823, 3, 109, 3, 7, 5, 13, 3,
    17, 643, 3, 7, 3, 11, 3, 3, 7, 3, 5, 3,
    29, 3, 5, 3, 157, 3, 43, 3, 5, 3, 19, 3,
    11, 3, 7, 3, 3, 3, 24019, 3, 3, 3, 1918507, 2354263,
    23, 3, 3, 7, 3, 5, 239, 3, 11, 3, 5, 74471,
    21701, 3, 5, 3, 3, 3, 11, 5, 13, 3, 5, 3,
    18217, 3, 3, 3, 89, 5, 3, 3, 3, 7, 6101, 11,
    3, 3, 179, 3, 3, 1987, 463, 3, 5, 3, 3, 61,
    79, 3, 3, 3, 11, 7, 3, 5, 3, 421, 3, 3,
    11, 3, 5, 557, 244759, 3, 5, 3, 2293, 3, 3, 3,
    3, 2162393, 5, 73, 3, 3, 7, 3, 11, 3, 13, 3,
    3, 7, 3, 3, 317, 1373, 3, 3023, 5, 3, 17, 5,
    3, 23, 3, 3, 5, 3, 149, 31, 5, 821, 7, 5,
    3, 353, 79, 3, 3, 13, 3, 7, 1003621, 3, 5, 3,
    41, 3, 3, 3, 3, 3, 5, 3, 673, 3, 3, 7,
    5, 3, 113, 3, 383, 109, 3, 7, 3, 5, 3, 3,
    3, 5, 3, 137, 3, 3, 5, 3, 2699, 881, 3, 5,
    3, 19, 17, 5, 3, 3, 13, 3, 7, 3, 23, 3,
    89, 3, 7, 845431, 5, 3, 3, 853, 3, 3, 47, 971,
    3, 3, 11, 13, 3, 5, 19, 3, 3, 3, 3, 3,
    11, 3, 3, 3, 2038943, 5, 3, 5, 67, 3, 59, 3,
    3, 5741, 3851, 3, 3, 5, 3, 7, 3, 3, 409, 3,
    7, 3, 109, 31, 5, 3, 13, 3, 3, 30971, 3, 5,
    37, 3, 19, 3, 79, 3, 11, 3, 3, 17, 623983, 3,
    5, 3, 5, 3, 3, 53, 193, 3, 3, 1579597, 3, 3,
    3, 29, 3, 3, 5, 3, 3, 3, 6899, 3, 13, 3,
    21587, 3, 7, 3, 31, 715903, 151, 7, 3, 3, 41, 3,
    7, 3, 5, 3, 53, 3482179, 19, 3, 3, 3, 23, 3,
    11, 3, 5, 3, 251, 191, 3, 17, 1123, 5, 22003, 3,
    3, 7, 5, 3, 3, 11, 3, 5, 3, 13, 3, 3,
    5, 3, 7, 3, 5, 3, 13, 3, 7, 877, 61, 3,
    19, 3, 3, 7, 13, 3, 11, 97, 3, 5, 3, 17,
    5, 3, 3, 23, 631, 5, 3, 3, 5, 3, 11, 79,
    3, 7, 3, 67, 5, 73, 3, 3, 23, 3, 5, 3,
    3, 3, 5, 3, 41, 3, 5, 3, 7, 3, 11, 23,
    3, 3, 7, 3, 3, 3307, 5, 3, 4957, 3, 3, 5,
    3, 3, 3, 11]

theorem prime_sub_4027 : Nat.Prime (12982270197518 - 4027) := by
  show Nat.Prime 12982270193491
  exact p12982270193491

theorem check_4027 : allC 12982270197518 4027 P10k ds_4027 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 12982270197518 is 4027. -/
theorem minGB_4027 : minGB 12982270197518 = 4027 :=
  minGB_eq_of P10k P10k_complete 12982270197518 4027 (by norm_num) (by norm_num) prime_sub_4027 ds_4027 check_4027

def ds_4057 : List ℕ := [
    2, 5, 3, 13, 3, 5, 3, 7, 3, 3, 47, 422407,
    3, 5, 3, 3, 3, 7, 37, 3, 5, 23, 3, 3,
    73, 3, 5, 3, 29, 3, 17, 3, 3, 401, 3, 11,
    5939, 5, 3, 3, 3, 7577, 3, 5, 3, 19, 1321, 5,
    3, 7, 3, 3, 13, 3, 3, 3, 3, 7, 197, 3,
    5, 3, 252589, 3, 5, 3, 17, 6203, 3, 11, 3, 3,
    1011779, 5, 31, 3, 3, 7, 3, 1163, 3, 67, 3, 5,
    7, 3, 3, 29, 3, 5, 3, 3, 317, 3, 139, 3,
    3, 3, 5, 19, 11, 3, 3, 3, 127, 2543, 3, 3,
    3, 463, 7, 5, 3, 41, 13, 3, 5, 3, 3, 3,
    167, 5, 3, 3, 7, 3, 13, 3, 431, 5, 17, 3,
    31, 9199, 3, 19, 3, 13, 3, 3, 11, 3, 5, 3,
    8009, 3, 5, 3, 7, 3, 11, 3, 5, 3, 23, 3,
    151, 3, 31, 3, 3, 3, 97, 3, 3, 3, 751, 19,
    11, 3, 3, 13, 3, 5, 1063, 3, 8369, 3, 5, 7,
    53, 3, 5, 3, 3, 3, 419, 5, 231169, 3, 5, 3,
    673513, 3, 3, 3, 449, 5, 3, 3, 3, 20749, 7, 17,
    3, 3, 7, 3, 3, 59, 49711, 3, 5, 3, 3, 7,
    29, 3, 3, 3, 691, 37, 3, 5, 3, 2693, 3, 3,
    7, 3, 5, 23, 11, 3, 5, 3, 7, 3, 3, 3,
    3, 7, 5, 97, 3, 3, 13, 3, 101113, 3, 23, 3,
    3, 331, 3, 3, 37, 67, 3, 7, 5, 3, 11, 5,
    3, 7, 3, 3, 5, 3, 7, 29867, 5, 17, 6421, 5,
    3, 199, 11, 3, 3, 1483, 3, 17, 7, 3, 5, 3,
    13, 3, 3, 3, 3, 3, 5, 3, 7, 3, 3, 2500783,
    5, 3, 11, 3, 23, 991, 3, 67, 3, 5, 3, 3,
    3, 5, 3, 165589, 3, 3, 5, 3, 11, 19, 3, 5,
    3, 7, 311, 5, 3, 3, 65839, 3, 31, 3, 19, 3,
    13, 3, 1496149, 7, 5, 3, 3, 491, 3, 3, 41, 13,
    3, 3, 7, 954727, 3, 5, 317, 3, 3, 3, 3, 3,
    1904533, 3, 3, 3, 32213, 5, 3, 5, 131, 3, 7, 3,
    3, 727, 1071739, 3, 3, 5, 3, 181, 3, 3, 6121, 3,
    11, 3, 129607, 17, 5, 3, 74623, 3, 3, 7, 3, 5,
    29, 3, 37, 3, 7, 3, 157, 3, 3, 7, 31, 3,
    5, 3, 5, 3, 3, 47, 11, 3, 3, 4003, 3, 3,
    3, 7, 3, 3, 5, 3, 3, 3, 13, 3, 7, 3,
    241, 3, 113, 3, 13, 59, 29, 41, 3, 3, 631, 3,
    11, 3, 5, 3, 7, 601, 11, 3, 3, 3, 811, 3,
    109, 3, 5, 3, 211597, 43, 3, 229, 131, 5, 11, 3,
    3, 479, 5, 3, 3, 13, 3, 5, 3, 17, 3, 3,
    5, 3, 409, 3, 5, 3, 1033, 3, 260269, 20011, 11, 3,
    23, 3, 3, 31, 7, 3, 2273, 41, 3, 5, 3, 6047,
    5, 3, 3, 7, 67, 5, 3, 3, 5, 3, 138059, 17,
    3, 157, 3, 31, 5, 14431, 3, 3, 59, 3, 5, 3,
    3, 3, 5, 3, 11, 3, 5, 3, 97, 3, 19387, 13,
    3, 3, 43487, 3, 3, 29383, 5, 3, 7, 3, 3, 5,
    3, 3, 3, 983, 287939, 3, 7]

theorem prime_sub_4057 : Nat.Prime (15197900994218 - 4057) := by
  show Nat.Prime 15197900990161
  exact p15197900990161

theorem check_4057 : allC 15197900994218 4057 P10k ds_4057 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 15197900994218 is 4057. -/
theorem minGB_4057 : minGB 15197900994218 = 4057 :=
  minGB_eq_of P10k P10k_complete 15197900994218 4057 (by norm_num) (by norm_num) prime_sub_4057 ds_4057 check_4057

def ds_4327 : List ℕ := [
    2, 109, 3, 55351, 3, 19, 3, 76829, 3, 3, 5, 7,
    3, 97523, 3, 3, 3, 5, 31, 3, 67, 7, 3, 3,
    3469, 3, 53, 3, 30559, 3, 13, 3, 3, 17123, 3, 5,
    827, 7, 3, 3, 3, 5, 3, 197, 3, 6163, 5, 239,
    3, 337, 3, 3, 5, 3, 3, 3, 3, 5, 12503, 3,
    13, 3, 619, 3, 11, 3, 5, 17, 3, 241, 3, 3,
    47, 7, 11, 3, 3, 319343, 3, 857, 3, 5, 3, 32971,
    13, 3, 3, 7, 3, 45289, 3, 3, 2579, 3, 7, 3,
    3, 3, 181, 5, 1039, 3, 3, 3, 5, 11, 3, 3,
    3, 5, 61, 12517, 3, 739, 5, 3, 11, 3, 3, 3,
    5, 13, 3, 3, 5, 3, 7, 3, 29, 293, 53, 3,
    5, 3191, 3, 907, 3, 43, 3, 3, 5, 3, 137, 3,
    13, 3, 157, 3, 2039, 3, 7, 3, 9791, 3, 11, 3,
    7, 3, 71, 3, 3, 3, 4483, 3, 3, 3, 5, 31,
    191, 3, 3, 5, 3, 1453, 11, 3, 5, 3, 13, 37,
    7, 3, 109, 3, 3, 3, 23, 4013, 7, 3, 17, 3,
    5, 3, 3, 3, 5, 7, 3, 3, 3, 5, 11, 29,
    3, 3, 67, 3, 3, 5, 7, 3, 11, 3, 3, 5,
    199, 3, 3, 3, 5, 292459, 3, 7, 3, 73, 3, 3,
    2854637, 3, 13, 17, 5, 3, 127, 3, 257, 3, 3, 3,
    3, 5, 294347, 7, 3, 3, 11, 3, 89, 3, 29, 3,
    3, 13, 3, 3, 5, 359, 3, 59, 17, 3, 23, 53,
    3, 11, 3, 3, 19, 3, 5, 109, 479, 7, 47, 4447,
    3, 71, 5, 3, 3, 5, 3, 5, 17, 3, 4109683, 3,
    631, 3, 3, 3, 3, 3, 509, 3, 5, 3, 3, 5270737,
    254389, 3, 13, 3, 5, 173, 3, 11, 3, 7, 3, 3,
    3, 23, 3, 4519, 3, 3, 31, 3, 5, 7, 3, 653,
    3, 5, 7, 971, 3, 3, 5, 3, 1913, 3, 5, 3,
    12781, 3, 5, 271, 11, 3, 3, 5, 3, 3, 5, 7,
    3, 3, 5, 17, 3, 37171, 7, 3, 3, 3, 3, 3,
    61, 3, 3, 3, 13, 7, 3, 227, 5, 3, 991, 3,
    3, 5, 7, 3, 3, 43, 3, 2803, 3, 3, 53, 3,
    2441, 3, 5, 233, 7, 3, 11, 3, 3, 169627, 3, 569,
    59, 3, 5, 3, 19, 3, 7, 3, 3, 5, 101, 3,
    61, 3, 23269, 3, 3, 5, 13, 3, 3, 11, 3, 3,
    3, 24029, 3, 3, 11, 3, 3, 3, 5, 3, 5, 3,
    7, 3, 251, 3, 23, 5, 37, 533831, 3, 3, 43, 3,
    5, 3, 29, 3, 13, 5, 7, 3, 3, 3, 11, 3,
    7, 3, 408631, 3, 4133, 5, 3, 5, 139, 7, 19, 3,
    3, 5, 448031, 3, 3, 5, 3, 633037, 3, 5, 3, 3,
    19, 3, 107, 3, 23, 3, 47, 3, 17, 5, 18329, 3,
    307, 3, 3, 5, 11, 3, 13, 5, 3, 249257, 3, 7,
    11, 3, 3, 5, 13, 7229, 3, 3, 2364409, 3, 5, 2237,
    3, 109, 3, 41, 7, 23, 3, 3, 127, 3, 13, 3,
    3, 3, 2309, 3, 113, 3, 83, 3, 11, 3, 19, 17,
    3, 3, 53, 3, 3, 5, 7, 3, 149, 3, 3, 19,
    3, 3, 3, 5, 7, 3, 5, 73, 3, 3, 3, 67,
    107, 5, 3, 2963, 3, 3, 7, 3, 31, 37, 5, 3,
    3, 41, 3, 5, 3, 54401, 3, 3, 5, 3, 11, 3,
    3, 1564907]

theorem prime_sub_4327 : Nat.Prime (28998050650046 - 4327) := by
  show Nat.Prime 28998050645719
  exact p28998050645719

theorem check_4327 : allC 28998050650046 4327 P10k ds_4327 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 28998050650046 is 4327. -/
theorem minGB_4327 : minGB 28998050650046 = 4327 :=
  minGB_eq_of P10k P10k_complete 28998050650046 4327 (by norm_num) (by norm_num) prime_sub_4327 ds_4327 check_4327

def ds_4519 : List ℕ := [
    2, 106363, 3, 5, 3, 73, 3, 17, 3, 3, 893873, 5,
    3, 7, 3, 3, 3, 11, 5, 3, 29, 457, 3, 3,
    5, 3, 103, 3, 307, 3, 5, 3, 3, 3643, 3, 139,
    5, 4231, 3, 3, 3, 149, 3, 11, 3, 1025119, 7, 17,
    3, 31, 3, 3, 127, 3, 3, 3, 3, 19, 5, 3,
    13, 3, 5, 3, 1087, 3, 23, 5, 3, 18217, 3, 3,
    5, 347, 7, 3, 3, 5, 3, 167, 3, 7, 3, 239,
    13, 3, 3, 5, 3, 7, 3, 3, 5, 3, 19, 3,
    3, 3, 11, 617, 5, 3, 3, 3, 541, 5, 3, 3,
    3, 31, 5, 19, 3, 1571, 7, 3, 661, 3, 3, 3,
    967, 7, 3, 3, 61, 3, 97, 3, 5, 17, 241, 3,
    13, 5, 3, 29, 3, 5, 3, 3, 310697, 3, 37, 3,
    13, 3, 11, 3, 131, 3, 5, 3, 7, 3, 5, 3,
    11, 3, 5, 3, 3, 3, 5, 3, 3, 3, 4621, 5,
    7, 3, 3, 23, 3, 25321, 17, 3, 7, 3, 13, 19,
    5, 3, 7, 3, 3, 3, 5, 21521, 613967, 3, 3727, 3,
    9421, 3, 3, 3, 207457, 1277557, 3, 3, 3, 1621, 5, 11,
    3, 3, 83, 3, 3, 29, 5, 3, 7, 3, 3, 107,
    5, 3, 3, 3, 11, 491, 3, 61, 3, 7, 3, 3,
    5, 3, 13, 53, 7, 3, 79, 3, 37, 3, 3, 3,
    3, 13, 240607, 17, 3, 3, 5, 3, 11, 3, 5, 3,
    3, 13, 3, 3, 1118021, 5, 3, 5, 431, 3, 2927, 240421,
    3, 191, 3, 3, 7, 3, 43481, 5, 17, 43, 5, 503,
    3, 61, 251431, 3, 3, 5711, 3, 499, 5, 3, 97, 3,
    421, 3, 3, 3, 3, 3, 7, 3, 307, 3, 3, 5,
    13417, 3, 13, 3, 67, 5, 3, 71, 3, 739, 3, 3,
    3, 827, 3, 31, 3, 3, 137, 3, 47, 5, 3, 7,
    3, 17, 41, 73, 3, 3, 5741, 3, 11, 3, 4639, 3,
    7, 3, 271, 5, 251, 3, 3, 7, 3, 3, 373, 5,
    3, 3, 11, 5, 3, 141529, 13, 3, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 1783, 3, 11, 7, 3, 23, 3,
    3, 19, 5, 3, 3, 9461, 3, 5, 3, 3, 5, 3,
    109, 3, 17, 5, 29, 3, 7, 3, 3, 5, 3, 1069,
    641, 3, 7, 3, 389273, 3, 5, 3, 3, 43, 5, 3,
    113, 3, 11, 3, 3, 14533, 5, 3, 3, 5, 3, 3,
    3, 5, 3, 3, 23, 3, 3, 3, 601, 3, 1226593, 3,
    31, 3, 5, 3, 43, 66863, 5, 17, 3, 3, 7, 3,
    19, 3, 11, 3, 13, 17, 5, 3, 3, 3, 5, 3,
    11, 3, 61, 3, 47, 83, 3, 151, 5, 109, 7, 3,
    3, 6529, 224261, 3, 3, 7, 3, 730447, 3, 31, 3, 3,
    419, 3, 5, 3, 19, 3, 863, 3, 9473, 559667, 5, 3,
    7, 3, 3, 47, 5, 3, 11, 7, 3, 114593, 3, 5,
    7, 3, 3, 241, 5, 23, 3, 3, 5387, 3, 11, 5,
    3, 37, 3, 5, 71, 7, 3, 3, 83, 3, 13, 3,
    3, 3, 7, 3, 5, 3, 79, 3, 5, 3, 11, 5,
    3, 3, 19, 3, 3, 37, 12263, 3, 5, 3, 3, 53,
    3, 3, 3, 11, 5, 3, 127, 5, 3, 3, 3, 2131,
    17, 9839, 3, 317, 3, 3, 11, 3, 7, 5, 7, 3,
    3, 11, 3, 30161, 3, 7, 3, 3, 13, 3, 619, 3,
    3, 5, 5, 3, 13, 3, 5, 263, 3, 3, 3, 3,
    3, 29, 1051, 5, 3, 3, 3, 3, 11, 3, 5, 43283,
    3]

theorem prime_sub_4519 : Nat.Prime (46878442766282 - 4519) := by
  show Nat.Prime 46878442761763
  exact p46878442761763

theorem check_4519 : allC 46878442766282 4519 P10k ds_4519 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 46878442766282 is 4519. -/
theorem minGB_4519 : minGB 46878442766282 = 4519 :=
  minGB_eq_of P10k P10k_complete 46878442766282 4519 (by norm_num) (by norm_num) prime_sub_4519 ds_4519 check_4519

def ds_4909 : List ℕ := [
    2, 5, 3, 67, 3, 5, 3, 7, 3, 3, 13, 661931,
    3, 5, 3, 3, 3, 7, 53, 3, 5, 76387, 3, 3,
    29, 3, 5, 3, 13, 3, 11, 3, 3, 577, 3, 71,
    16729, 5, 3, 3, 3, 43, 3, 5, 3, 4241, 3628357, 5,
    3, 7, 3, 3, 47, 3, 3, 3, 3, 7, 5905021, 3,
    5, 3, 17, 3, 5, 3, 141851, 383, 3, 599, 3, 3,
    389, 5, 73, 3, 3, 7, 3, 17, 3, 13, 3, 5,
    7, 3, 3, 11, 3, 5, 3, 3, 2678983, 3, 13, 3,
    3, 3, 5, 1009, 1217, 3, 3, 3, 11027, 13, 3, 3,
    3, 5323, 7, 5, 3, 29, 157, 3, 5, 3, 3, 3,
    23, 5, 3, 3, 7, 3, 109, 3, 149, 5, 19, 3,
    101, 379, 3, 5407, 3, 11, 3, 3, 13, 3, 5, 3,
    263, 3, 5, 3, 7, 3, 337, 3, 5, 3, 89, 3,
    11, 3, 23, 3, 3, 3, 13, 3, 3, 3, 31, 2446981,
    1091, 3, 3, 17, 3, 5, 103, 3, 11, 3, 5, 7,
    47, 3, 5, 3, 3, 3, 11, 5, 937, 3, 5, 3,
    127, 3, 3, 3, 13, 5, 3, 3, 3, 151, 7, 11,
    3, 3, 7, 3, 3, 6229, 131, 3, 5, 3, 3, 7,
    17, 3, 3, 3, 11, 268883, 3, 5, 3, 17, 3, 3,
    7, 3, 5, 751, 43, 3, 5, 3, 7, 3, 3, 3,
    3, 7, 5, 31, 3, 3, 2219683, 3, 11, 3, 41203, 3,
    3, 220681, 3, 3, 149, 23, 3, 7, 5, 3, 13, 5,
    3, 7, 3, 3, 5, 3, 7, 13, 5, 2063, 11, 5,
    3, 61, 3579133, 3, 3, 40823, 3, 571, 7, 3, 5, 3,
    19, 3, 3, 3, 3, 3, 5, 3, 7, 3, 3, 43,
    5, 3, 229, 3, 29, 67, 3, 59, 3, 5, 3, 3,
    3, 5, 3, 1051, 3, 3, 5, 3, 37, 13, 3, 5,
    3, 7, 23, 5, 3, 3, 19, 3, 11, 3, 641, 3,
    97, 3, 71, 7, 5, 3, 3, 211, 3, 3, 41, 17,
    3, 3, 7, 277, 3, 5, 193, 3, 3, 3, 3, 3,
    11, 3, 3, 3, 83, 5, 3, 5, 61, 3, 7, 3,
    3, 17, 1861, 3, 3, 5, 3, 8111, 3, 3, 307, 3,
    439, 3, 109, 19, 5, 3, 78203, 3, 3, 7, 3, 5,
    15559, 3, 23, 3, 7, 3, 11, 3, 3, 7, 37, 3,
    5, 3, 5, 3, 3, 31, 17, 3, 3, 61, 3, 3,
    3, 7, 3, 3, 5, 3, 3, 3, 2657, 3, 7, 3,
    19, 3, 31, 3, 311, 17, 8329, 41, 3, 3, 373, 3,
    107, 3, 5, 3, 7, 1193, 1693, 3, 3, 3, 3169, 3,
    11, 3, 5, 3, 2003, 4423, 3, 8369, 13, 5, 1847, 3,
    3, 7753, 5, 3, 3, 11, 3, 5, 3, 4357, 3, 3,
    5, 3, 127, 3, 5, 3, 17, 3, 163, 103, 11821, 3,
    1609, 3, 3, 13, 7, 3, 11, 17, 3, 5, 3, 659,
    5, 3, 3, 7, 113, 5, 3, 3, 5, 3, 11, 13,
    3, 79, 3, 29927, 5, 1831, 3, 3, 617, 3, 5, 3,
    3, 3, 5, 3, 270899, 3, 5, 3, 17, 3, 11, 37,
    3, 3, 1289, 3, 3, 13, 5, 3, 7, 3, 3, 5,
    3, 3, 3, 11, 67, 3, 7, 547, 3, 3, 3, 5,
    29, 23, 3, 37, 3, 3, 5, 3, 19, 7, 53, 3,
    3, 7, 3, 1547573, 3, 5, 3, 3, 7, 3, 5, 3,
    3, 338263, 449, 3, 31, 3, 6373, 5, 3, 3, 3, 3,
    3, 5, 131, 29, 3, 3, 3, 3, 5, 3, 59, 5,
    3, 53, 3, 3, 11, 283, 43, 3, 17, 7, 5, 29,
    3, 7, 3, 3, 811, 79, 5, 3, 3, 3, 3, 3,
    5, 19, 3, 3, 73, 5, 3, 13, 3, 3, 23, 5,
    3, 67, 59, 3, 3, 3, 5]

theorem prime_sub_4909 : Nat.Prime (76903574497118 - 4909) := by
  show Nat.Prime 76903574492209
  exact p76903574492209

theorem check_4909 : allC 76903574497118 4909 P10k ds_4909 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 76903574497118 is 4909. -/
theorem minGB_4909 : minGB 76903574497118 = 4909 :=
  minGB_eq_of P10k P10k_complete 76903574497118 4909 (by norm_num) (by norm_num) prime_sub_4909 ds_4909 check_4909

def ds_5077 : List ℕ := [
    2, 5, 3, 37, 3, 5, 3, 11, 3, 3, 19, 71,
    3, 5, 3, 3, 3, 1193, 137, 3, 5, 70181, 3, 3,
    7, 3, 5, 3, 223, 3, 227, 3, 3, 7, 3, 11,
    31, 5, 3, 3, 3, 7, 3, 5, 3, 13, 523, 5,
    3, 37, 3, 3, 113, 3, 3, 3, 3, 1082093, 13, 3,
    5, 3, 7, 3, 5, 3, 23, 59, 3, 7, 3, 3,
    4951, 5, 169151, 3, 3, 10159, 3, 41, 3, 17, 3, 5,
    781999, 3, 3, 5210063, 3, 5, 3, 3, 19, 3, 187471, 3,
    3, 3, 5, 2011, 11, 3, 3, 3, 1753, 349, 3, 3,
    3, 7, 23, 5, 3, 133493, 499, 3, 5, 3, 3, 3,
    14639, 5, 3, 3, 59, 3, 7433, 3, 7, 5, 1427, 3,
    75337, 257, 3, 7, 3, 77899, 3, 3, 7, 3, 5, 3,
    17, 3, 5, 3, 2772137, 3, 11, 3, 5, 3, 1291, 3,
    113, 3, 7, 3, 3, 3, 116903, 3, 3, 3, 40361, 4483,
    11, 3, 3, 7, 3, 5, 79133, 3, 67, 3, 5, 2903,
    31, 3, 5, 3, 3, 3, 37, 5, 73, 3, 5, 3,
    19, 3, 3, 3, 3475951, 5, 3, 3, 3, 7, 17, 167,
    3, 3, 191, 3, 3, 13, 23, 3, 5, 3, 3, 193,
    47, 3, 3, 3, 4614433, 7, 3, 5, 3, 61, 3, 3,
    13, 3, 5, 31, 11, 3, 5, 3, 227, 3, 3, 3,
    3, 151, 5, 53, 3, 3, 7, 3, 1069, 3, 113, 3,
    3, 7, 3, 3, 367, 19, 3, 10344107, 5, 3, 11, 5,
    3, 229, 3, 3, 5, 3, 19, 17, 5, 13, 7, 5,
    3, 293, 11, 3, 3, 31, 3, 7, 11, 3, 5, 3,
    4129, 3, 3, 3, 3, 3, 5, 3, 17, 3, 3, 7,
    5, 3, 11, 3, 599, 31, 3, 7, 3, 5, 3, 3,
    3, 5, 3, 29, 3, 3, 5, 3, 11, 1249, 3, 5,
    3, 61, 103, 5, 3, 3, 173, 3, 7, 3, 43, 3,
    181, 3, 7, 1297, 5, 3, 3, 19, 3, 3, 9133, 1459,
    3, 3, 6285887, 41, 3, 5, 31, 3, 3, 3, 3, 3,
    29, 3, 3, 3, 5281, 5, 3, 5, 1087, 3, 13, 3,
    3, 277, 313, 3, 3, 5, 3, 7, 3, 3, 3761, 3,
    7, 3, 37, 23, 5, 3, 89123, 3, 3, 362759, 3, 5,
    1061, 3, 475529, 3, 829, 3, 17, 3, 3, 11, 103, 3,
    5, 3, 5, 3, 3, 13, 11, 3, 3, 1049, 3, 3,
    3, 79, 3, 3, 5, 3, 3, 3, 17, 3, 97, 3,
    47, 3, 7, 3, 4057, 67, 977, 7, 3, 3, 19, 3,
    7, 3, 5, 3, 59, 131, 11, 3, 3, 3, 17011, 3,
    23, 3, 5, 3, 61, 153353, 3, 47, 29, 5, 11, 3,
    3, 7, 5, 3, 3, 41, 3, 5, 3, 79, 3, 3,
    5, 3, 7, 3, 5, 3, 269, 3, 7, 89, 11, 3,
    10211, 3, 3, 7, 293, 3, 37, 149, 3, 5, 3, 41,
    5, 3, 3, 13, 83, 5, 3, 3, 5, 3, 31, 247249,
    3, 7, 3, 20177, 5, 5807, 3, 3, 5717, 3, 5, 3,
    3, 3, 5, 3, 11, 3, 5, 3, 7, 3, 17, 19,
    3, 3, 7, 3, 3, 401, 5, 3, 131, 3, 3, 5,
    3, 3, 3, 13, 6022769, 3, 899753, 23, 3, 3, 3, 5,
    13, 11, 3, 7, 3, 3, 5, 3, 1117, 11, 409, 3,
    3, 1129, 3, 59, 3, 5, 3, 3, 139, 3, 5, 3,
    3, 7, 100823, 3, 7, 3, 61, 5, 3, 3, 3, 3,
    3, 5, 11, 37, 3, 3, 3, 3, 5, 3, 7, 5,
    3, 1383451, 3, 3, 7, 2191513, 13, 3, 7, 15053, 5, 31,
    3, 11, 3, 3, 103, 2062339, 5, 3, 3, 3, 3, 3,
    5, 53, 3, 3, 7, 5, 3, 15083, 3, 3, 7, 5,
    3, 43, 199, 3, 3, 3, 5, 17, 3, 3, 5, 3,
    3, 557, 13, 3, 7, 3, 113, 5, 137, 3, 3, 7,
    3, 5, 3, 3, 145193]

theorem prime_sub_5077 : Nat.Prime (184162477860248 - 5077) := by
  show Nat.Prime 184162477855171
  exact p184162477855171

theorem check_5077 : allC 184162477860248 5077 P10k ds_5077 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 184162477860248 is 5077. -/
theorem minGB_5077 : minGB 184162477860248 = 5077 :=
  minGB_eq_of P10k P10k_complete 184162477860248 5077 (by norm_num) (by norm_num) prime_sub_5077 ds_5077 check_5077

def ds_5209 : List ℕ := [
    2, 5, 3, 31, 3, 5, 3, 119299, 3, 3, 23, 83,
    3, 5, 3, 3, 3, 41, 11, 3, 5, 107, 3, 3,
    7, 3, 5, 3, 829, 3, 19, 3, 3, 7, 3, 13,
    15761, 5, 3, 3, 3, 7, 3, 5, 3, 11, 137, 5,
    3, 13, 3, 3, 19, 3, 3, 3, 3, 2711, 439, 3,
    5, 3, 7, 3, 5, 3, 11, 73, 3, 7, 3, 3,
    7649, 5, 31, 3, 3, 11, 3, 3329, 3, 359, 3, 5,
    43, 3, 3, 672073, 3, 5, 3, 3, 1013, 3, 67, 3,
    3, 3, 5, 13, 29, 3, 3, 3, 978349, 37, 3, 3,
    3, 7, 17, 5, 3, 13, 4969, 3, 5, 3, 3, 3,
    11, 5, 3, 3, 211, 3, 17, 3, 7, 5, 547, 3,
    31, 523, 3, 7, 3, 53, 3, 3, 7, 3, 5, 3,
    316621, 3, 5, 3, 11, 3, 2224267, 3, 5, 3, 118163, 3,
    719, 3, 7, 3, 3, 3, 5297, 3, 3, 3, 11, 23,
    13, 3, 3, 7, 3, 5, 19, 3, 269, 3, 5, 29,
    13, 3, 5, 3, 3, 3, 17, 5, 74453, 3, 5, 3,
    109, 3, 3, 3, 257, 5, 3, 3, 3, 7, 1193, 1621,
    3, 3, 5534929, 3, 3, 41, 8221, 3, 5, 3, 3, 11,
    7877, 3, 3, 3, 19, 7, 3, 5, 3, 89, 3, 3,
    21503, 3, 5, 236981, 43, 3, 5, 3, 5639, 3, 3, 3,
    3, 83, 5, 23, 3, 3, 7, 3, 4130323, 3, 9547, 3,
    3, 7, 3, 3, 8297, 17, 3, 61, 5, 3, 307, 5,
    3, 127, 3, 3, 5, 3, 53, 7537, 5, 10177, 7, 5,
    3, 13, 263, 3, 3, 17, 3, 7, 13, 3, 5, 3,
    457, 3, 3, 3, 3, 3, 5, 3, 19, 3, 3, 7,
    5, 3, 71, 3, 379, 179, 3, 7, 3, 5, 3, 3,
    3, 5, 3, 73, 3, 3, 5, 3, 37, 17, 3, 5,
    3, 1597, 11, 5, 3, 3, 59, 3, 7, 3, 3911, 3,
    701, 3, 7, 29, 5, 3, 3, 11, 3, 3, 17, 151,
    3, 3, 11616551, 11, 3, 5, 61, 3, 3, 3, 3, 3,
    10289, 3, 3, 3, 149, 5, 3, 5, 19, 3, 907, 3,
    3, 7907, 599153, 3, 3, 5, 3, 7, 3, 3, 13, 3,
    7, 3, 7170689, 137, 5, 3, 79, 3, 3, 11, 3, 5,
    2063, 3, 349, 3, 17, 3, 41, 3, 3, 23, 31, 3,
    5, 3, 5, 3, 3, 17, 2477, 3, 3, 2056253, 3, 3,
    3, 373, 3, 3, 5, 3, 3, 3, 11, 3, 7283, 3,
    37, 3, 7, 3, 1523, 97, 23, 7, 3, 3, 139, 3,
    7, 3, 5, 3, 11, 643, 227, 3, 3, 3, 202381, 3,
    2677, 3, 5, 3, 17, 13, 3, 11, 193, 5, 19, 3,
    3, 7, 5, 3, 3, 17, 3, 5, 3, 70487, 3, 3,
    5, 3, 7, 3, 5, 3, 507961, 3, 7, 307, 660281, 3,
    653, 3, 3, 7, 19, 3, 431, 64817, 3, 5, 3, 1069,
    5, 3, 3, 11, 59, 5, 3, 3, 5, 3, 103, 11,
    3, 7, 3, 31, 5, 13, 3, 3, 17, 3, 5, 3,
    3, 3, 5, 3, 1543, 3, 5, 3, 7, 3, 19, 37,
    3, 3, 7, 3, 3, 107, 5, 3, 53, 3, 3, 5,
    3, 3, 3, 83, 11, 3, 13, 12829, 3, 3, 3, 5,
    31, 79, 3, 7, 3, 3, 5, 3, 11, 17, 29, 3,
    3, 61, 3, 19, 3, 5, 3, 3, 63029, 3, 5, 3,
    3, 7, 10574491, 3, 7, 3, 11, 5, 3, 3, 3, 3,
    3, 5, 13, 23, 3, 3, 3, 3, 5, 3, 7, 5,
    3, 13, 3, 3, 7, 113, 43, 3, 7, 13, 5, 11,
    3, 5381, 3, 3, 1823, 31, 5, 3, 3, 3, 3, 3,
    5, 359, 3, 3, 7, 5, 3, 17, 3, 3, 7, 5,
    3, 13, 23, 3, 3, 3, 5, 13, 3, 3, 5, 3,
    3, 11, 263, 3, 7, 3, 13, 5, 23, 3, 3, 7,
    3, 5, 3, 3, 79, 4388689, 3, 3, 3, 18149, 106669, 5,
    509, 3, 3, 89, 3, 7, 3, 17]

theorem prime_sub_5209 : Nat.Prime (217361316706568 - 5209) := by
  show Nat.Prime 217361316701359
  exact p217361316701359

theorem check_5209 : allC 217361316706568 5209 P10k ds_5209 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 217361316706568 is 5209. -/
theorem minGB_5209 : minGB 217361316706568 = 5209 :=
  minGB_eq_of P10k P10k_complete 217361316706568 5209 (by norm_num) (by norm_num) prime_sub_5209 ds_5209 check_5209

def ds_5569 : List ℕ := [
    2, 5, 3, 131, 3, 5, 3, 41, 3, 3, 7, 13,
    3, 5, 3, 3, 3, 19, 2549, 3, 5, 31, 3, 3,
    11, 3, 5, 3, 662353, 3, 36007, 3, 3, 22039, 3, 6571,
    7, 5, 3, 3, 3, 602999, 3, 5, 3, 7, 157, 5,
    3, 11, 3, 3, 7, 3, 3, 3, 3, 13, 7547, 3,
    5, 3, 9403, 3, 5, 3, 67, 101, 3, 13, 3, 3,
    7, 5, 239, 3, 3, 23, 3, 7, 3, 503, 3, 5,
    907, 3, 3, 109, 3, 5, 3, 3, 199, 3, 241, 3,
    3, 3, 5, 43, 37, 3, 3, 3, 29, 7, 3, 3,
    3, 4363, 761, 5, 3, 7, 19, 3, 5, 3, 3, 3,
    7, 5, 3, 3, 11, 3, 523, 3, 19009, 5, 13, 3,
    17521279, 11, 3, 17, 3, 7, 3, 3, 23, 3, 5, 3,
    7, 3, 5, 3, 19, 3, 269, 3, 5, 3, 6911, 3,
    29, 3, 5297, 3, 3, 3, 97, 3, 3, 3, 37, 7,
    31, 3, 3, 11, 3, 5, 7, 3, 13, 3, 5, 1753,
    11, 3, 5, 3, 3, 3, 17791, 5, 13, 3, 5, 3,
    233, 3, 3, 3, 19, 5, 3, 3, 3, 7639, 197, 7,
    3, 3, 17, 3, 3, 7, 4824151, 3, 5, 3, 3, 983,
    223, 3, 3, 3, 17, 4693177, 3, 5, 3, 19, 3, 3,
    1802707, 3, 5, 7, 1281431, 3, 5, 3, 35027, 3, 3, 3,
    3, 2887, 5, 11, 3, 3, 31, 3, 131, 3, 13, 3,
    3, 151, 3, 3, 2785301, 7, 3, 19, 5, 3, 7, 5,
    3, 73, 3, 3, 5, 3, 41, 11, 5, 89, 23, 5,
    3, 17, 21341, 3, 3, 13, 3, 41341, 16903, 3, 5, 3,
    7, 3, 3, 3, 3, 3, 5, 3, 53, 3, 3, 13,
    5, 3, 19, 3, 11, 251, 3, 433, 3, 5, 3, 3,
    3, 5, 3, 7, 3, 3, 5, 3, 7, 29, 3, 5,
    3, 8443, 14631103, 5, 3, 3, 13, 3, 853, 3, 3779, 3,
    53, 3, 59, 39829, 5, 3, 3, 29, 3, 3, 7, 43,
    3, 3, 47, 13, 3, 5, 2017, 3, 3, 3, 3, 3,
    49481, 3, 3, 3, 7, 5, 3, 5, 211, 3, 11, 3,
    3, 7, 113, 3, 3, 5, 3, 1201, 3, 3, 13123349, 3,
    29, 3, 11, 7, 5, 3, 13, 3, 3, 17, 3, 5,
    7, 3, 95581, 3, 347, 3, 13, 3, 3, 293, 19, 3,
    5, 3, 5, 3, 3, 1804819, 1605269, 3, 3, 7, 3, 3,
    3, 409, 3, 3, 5, 3, 3, 3, 7, 3, 11, 3,
    23, 3, 157, 3, 48847, 2399, 11, 13, 3, 3, 294761, 3,
    43, 3, 5, 3, 1151, 7, 173, 3, 3, 3, 17, 3,
    137, 3, 5, 3, 2663, 449, 3, 1871, 7, 5, 17, 3,
    3, 11, 5, 3, 3, 89, 3, 5, 3, 7, 3, 3,
    5, 3, 383, 3, 5, 3, 13, 3, 47, 1064669, 7, 3,
    11, 3, 3, 53, 13, 3, 7, 23, 3, 5, 3, 61,
    5, 3, 3, 3504437, 43, 5, 3, 3, 5, 3, 181, 59,
    3, 19, 3, 7, 5, 7209011, 3, 3, 7, 3, 5, 3,
    3, 3, 5, 3, 23, 3, 5, 3, 29, 3, 73, 401,
    3, 3, 479, 3, 3, 17, 5, 3, 233, 3, 3, 5,
    3, 3, 3, 7, 587, 3, 19, 11, 3, 3, 3, 5,
    37, 947, 3, 379, 3, 3, 5, 3, 602521, 53, 41, 3,
    3, 2576983, 3, 7, 3, 5, 3, 3, 23, 3, 5, 3,
    3, 7129, 13, 3, 17, 3, 7, 5, 3, 3, 3, 3,
    3, 5, 7, 41, 3, 3, 3, 3, 5, 3, 19, 5,
    3, 11, 3, 3, 293, 13, 7, 3, 113, 977, 5, 19,
    3, 13, 3, 3, 7, 149, 5, 3, 3, 3, 3, 3,
    5, 31, 3, 3, 59, 5, 3, 337, 3, 3, 9127, 5,
    3, 347, 7, 3, 3, 3, 5, 47, 3, 3, 5, 3,
    3, 13, 130211, 3, 2837, 3, 7, 5, 317, 3, 3, 1103,
    3, 5, 3, 3, 2085037, 19, 3, 3, 3, 31, 13, 5,
    52541, 3, 3, 6037, 3, 11, 3, 7, 37, 23, 3, 5,
    3, 3, 3, 3, 7, 3, 3, 3, 5, 3, 1581191, 3,
    3, 3, 3, 3, 7, 5, 3, 13, 37, 61, 3, 5,
    7, 3, 3, 10361501, 3, 3, 5, 3, 3, 5081, 857, 3,
    67, 5]

theorem prime_sub_5569 : Nat.Prime (389965026819938 - 5569) := by
  show Nat.Prime 389965026814369
  exact p389965026814369

theorem check_5569 : allC 389965026819938 5569 P10k ds_5569 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 389965026819938 is 5569. -/
theorem minGB_5569 : minGB 389965026819938 = 5569 :=
  minGB_eq_of P10k P10k_complete 389965026819938 5569 (by norm_num) (by norm_num) prime_sub_5569 ds_5569 check_5569

def ds_6469 : List ℕ := [
    2, 5, 3, 17, 3, 5, 3, 89, 3, 3, 7, 11864441,
    3, 5, 3, 3, 3, 53, 127, 3, 5, 193, 3, 3,
    19, 3, 5, 3, 17, 3, 5521, 3, 3, 23, 3, 67,
    7, 5, 3, 3, 3, 6576431, 3, 5, 3, 7, 13, 5,
    3, 103, 3, 3, 7, 3, 3, 3, 3, 1153, 23, 3,
    5, 3, 37, 3, 5, 3, 36923, 521, 3, 29, 3, 3,
    7, 5, 53, 3, 3, 61, 3, 7, 3, 11, 3, 5,
    19, 3, 3, 17608397, 3, 5, 3, 3, 11, 3, 4184629, 3,
    3, 3, 5, 47, 443, 3, 3, 3, 647, 7, 3, 3,
    3, 13, 1601, 5, 3, 7, 322669, 3, 5, 3, 3, 3,
    7, 5, 3, 3, 23, 3, 14057, 3, 15053, 5, 1433, 3,
    11, 13, 3, 443711, 3, 7, 3, 3, 83, 3, 5, 3,
    7, 3, 5, 3, 277, 3, 3541, 3, 5, 3, 43, 3,
    14732741, 3, 3001, 3, 3, 3, 23, 3, 3, 3, 13, 7,
    19, 3, 3, 2876983, 3, 5, 7, 3, 5866661, 3, 5, 13,
    89, 3, 5, 3, 3, 3, 79, 5, 17, 3, 5, 3,
    199, 3, 3, 3, 5341627, 5, 3, 3, 3, 17, 19, 7,
    3, 3, 11, 3, 3, 7, 1235833, 3, 5, 3, 3, 1249,
    59, 3, 3, 3, 13, 2791, 3, 5, 3, 613, 3, 3,
    65029, 3, 5, 7, 167, 3, 5, 3, 337, 3, 3, 3,
    3, 3198257, 5, 271, 3, 3, 29, 3, 19, 3, 809, 3,
    3, 11, 3, 3, 89, 7, 3, 23, 5, 3, 7, 5,
    3, 3637, 3, 3, 5, 3, 11, 131, 5, 67, 6053, 5,
    3, 13828271, 881, 3, 3, 890159, 3, 37, 1993, 3, 5, 3,
    7, 3, 3, 3, 3, 3, 5, 3, 47, 3, 3, 487,
    5, 3, 31, 3, 241, 433, 3, 6784039, 3, 5, 3, 3,
    3, 5, 3, 7, 3, 3, 5, 3, 7, 11, 3, 5,
    3, 13, 661, 5, 3, 3, 313, 3, 13, 3, 17, 3,
    11, 3, 8823181, 53, 5, 3, 3, 1949, 3, 3, 7, 23,
    3, 3, 31, 19, 3, 5, 59, 3, 3, 3, 3, 3,
    29, 3, 3, 3, 7, 5, 3, 5, 277, 3, 79, 3,
    3, 7, 17, 3, 3, 5, 3, 41, 3, 3, 2161, 3,
    17, 3, 78059, 7, 5, 3, 89, 3, 3, 13, 3, 5,
    7, 3, 11, 3, 37, 3, 2903, 3, 3, 859, 11, 3,
    5, 3, 5, 3, 3, 149, 242059, 3, 3, 7, 3, 3,
    3, 1987, 3, 3, 5, 3, 3, 3, 7, 3, 2017, 3,
    13, 3, 23, 3, 1697, 11, 17, 47, 3, 3, 41, 3,
    293071, 3, 5, 3, 17, 7, 77783, 3, 3, 3, 907, 3,
    43, 3, 5, 3, 11, 17, 3, 31, 7, 5, 103, 3,
    3, 13, 5, 3, 3, 47, 3, 5, 3, 7, 3, 3,
    5, 3, 11, 3, 5, 3, 3169, 3, 13687, 337, 7, 3,
    2213, 3, 3, 12246383, 5107, 3, 7, 2928769, 3, 5, 3, 3928259,
    5, 3, 3, 19, 37, 5, 3, 3, 5, 3, 61, 71,
    3, 16747, 3, 7, 5, 10729, 3, 3, 7, 3, 5, 3,
    3, 3, 5, 3, 41, 3, 5, 3, 13, 3, 2521, 197,
    3, 3, 11, 3, 3, 45247, 5, 3, 379, 3, 3, 5,
    3, 3, 3, 7, 1201, 3, 11, 61, 3, 3, 3, 5,
    313, 13, 3, 317, 3, 3, 5, 3, 59, 29, 19, 3,
    3, 643, 3, 7, 3, 5, 3, 3, 43, 3, 5, 3,
    3, 83, 5407, 3, 41, 3, 7, 5, 3, 3, 3, 3,
    3, 5, 7, 11, 3, 3, 3, 3, 5, 3, 3079, 5,
    3, 43, 3, 3, 71, 20705203, 7, 3, 3145741, 17, 5, 5659,
    3, 127, 3, 3, 7, 13, 5, 3, 3, 3, 3, 3,
    5, 181, 3, 3, 233, 5, 3, 31, 3, 3, 17, 5,
    3, 23, 7, 3, 3, 3, 5, 11, 3, 3, 5, 3,
    3, 4253, 3671, 3, 13, 3, 7, 5, 19, 3, 3, 113,
    3, 5, 3, 3, 3953993, 41, 3, 3, 3, 419, 11, 5,
    5245921, 3, 3, 9341, 3, 73, 3, 7, 17, 19, 3, 5,
    3, 3, 3, 3, 7, 3, 3, 3, 5, 3, 31, 3,
    3, 3, 3, 3, 7, 5, 3, 457, 9643, 11, 3, 5,
    7, 3, 3, 167, 3, 3, 5, 3, 3, 23, 14713, 3,
    31729, 5, 11, 3, 463, 3, 5, 3, 601, 2693, 3, 5,
    3, 7, 3, 5, 97, 3, 7, 3, 3, 3533, 3, 5,
    13, 67, 3, 83, 3, 3, 3, 17, 7, 89849, 3, 3,
    788399, 37, 3, 3, 7, 3, 168293, 3, 3, 5, 3, 3,
    5, 3, 3, 31574453, 3, 3, 7, 5, 3, 3, 43, 5,
    7, 3, 29, 3, 3, 7, 3, 5, 3, 173, 5, 3,
    3, 109, 3, 23, 13, 3, 11, 7, 3, 3, 3, 97,
    31, 3, 3, 37, 3, 3, 3, 3, 281, 5, 3, 3,
    11, 19, 5, 9013, 3, 18587, 53, 11, 3, 13]

theorem prime_sub_6469 : Nat.Prime (1047610575836828 - 6469) := by
  show Nat.Prime 1047610575830359
  exact p1047610575830359

theorem check_6469 : allC 1047610575836828 6469 P10k ds_6469 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 1047610575836828 is 6469. -/
theorem minGB_6469 : minGB 1047610575836828 = 6469 :=
  minGB_eq_of P10k P10k_complete 1047610575836828 6469 (by norm_num) (by norm_num) prime_sub_6469 ds_6469 check_6469

def ds_6961 : List ℕ := [
    2, 5, 3, 13, 3, 5, 3, 11, 3, 3, 17, 29,
    3, 5, 3, 3, 3, 1931, 7, 3, 5, 41, 3, 3,
    89, 3, 5, 3, 7, 3, 283, 3, 3, 207509, 3, 7,
    101, 5, 3, 3, 3, 47, 3, 5, 3, 49177, 29, 5,
    3, 467, 3, 3, 13, 3, 3, 3, 3, 167, 7, 3,
    5, 3, 911, 3, 5, 3, 563, 17, 3, 11, 3, 3,
    37, 5, 5850259, 3, 3, 13, 3, 67, 3, 1091, 3, 5,
    17, 3, 3, 35380607, 3, 5, 3, 3, 7, 3, 401, 3,
    3, 3, 5, 17, 11, 3, 3, 3, 7, 241, 3, 3,
    3, 19, 2620897, 5, 3, 23, 13, 3, 5, 3, 3, 3,
    3221, 5, 3, 3, 16651, 3, 13, 3, 2083, 5, 7, 3,
    227, 23, 3, 173, 3, 13, 3, 3, 11, 3, 5, 3,
    19, 3, 5, 3, 112771, 3, 11, 3, 5, 3, 7, 3,
    197, 3, 149, 3, 3, 3, 35344961, 3, 3, 3, 7, 3319,
    11, 3, 3, 13, 3, 5, 47416909, 3, 17, 3, 5, 139,
    2053, 3, 5, 3, 3, 3, 7, 5, 6703, 3, 5, 3,
    19, 3, 3, 3, 7, 5, 3, 3, 3, 51031, 79, 2861,
    3, 3, 70621, 3, 3, 643, 145799, 3, 5, 3, 3, 76717,
    7, 3, 3, 3, 210169, 19, 3, 5, 3, 29, 3, 3,
    23, 3, 5, 17, 11, 3, 5, 3, 13, 3, 3, 3,
    3, 613, 5, 193, 3, 3, 13, 3, 7, 3, 1827817, 3,
    3, 25913, 3, 3, 7, 19, 3, 73, 5, 3, 11, 5,
    3, 37, 3, 3, 5, 3, 19, 7, 5, 826667, 29, 5,
    3, 7, 11, 3, 3, 7, 3, 23, 11, 3, 5, 3,
    13, 3, 3, 3, 3, 3, 5, 3, 29, 3, 3, 1411769,
    5, 3, 7, 3, 156371, 67, 3, 19037, 3, 5, 3, 3,
    3, 5, 3, 43, 3, 3, 5, 3, 11, 23, 3, 5,
    3, 163, 3389, 5, 3, 3, 2591, 3, 1231, 3, 7, 3,
    13, 3, 9923, 3109, 5, 3, 3, 19, 3, 3, 947, 13,
    3, 3, 61, 7, 3, 5, 293, 3, 3, 3, 3, 3,
    47, 3, 3, 3, 2753, 5, 3, 5, 2917, 3, 19, 3,
    3, 23, 14173, 3, 3, 5, 3, 155581, 3, 3, 29, 3,
    11, 3, 7, 307, 5, 3, 23, 3, 3, 193, 3, 5,
    47, 3, 439, 3, 53, 3, 19, 3, 3, 11, 7, 3,
    5, 3, 5, 3, 3, 70006003, 11, 3, 3, 17, 3, 3,
    3, 827, 3, 3, 5, 3, 3, 3, 13, 3, 47, 3,
    71, 3, 199, 3, 7, 4297, 53, 373, 3, 3, 19, 3,
    11, 3, 5, 3, 29, 4051, 11, 3, 3, 3, 7, 3,
    3119, 3, 5, 3, 7, 72673, 3, 7, 113, 5, 11, 3,
    3, 239, 5, 3, 3, 13, 3, 5, 3, 1879, 3, 3,
    5, 3, 1307, 3, 5, 3, 7, 3, 17, 7, 11, 3,
    5479, 3, 3, 151, 1259, 3, 2478517, 131, 3, 5, 3, 79,
    5, 3, 3, 109, 7, 5, 3, 3, 5, 3, 29, 37,
    3, 83, 3, 107, 5, 271, 3, 3, 41, 3, 5, 3,
    3, 3, 5, 3, 7, 3, 5, 3, 362233, 3, 7, 13,
    3, 3, 37, 3, 3, 7, 5, 3, 6983, 3, 3, 5,
    3, 3, 3, 19, 67, 3, 2950159, 7, 3, 3, 3, 5,
    7, 11, 3, 47, 3, 3, 5, 3, 8629, 11, 61, 3,
    3, 13, 3, 199, 3, 5, 3, 3, 41, 3, 5, 3,
    3, 13, 919, 3, 53, 3, 131, 5, 3, 3, 3, 3,
    3, 5, 11, 151, 3, 3, 3, 3, 5, 3, 11, 5,
    3, 7, 3, 3, 59, 7, 61, 3, 19, 29536421, 5, 17,
    3, 11, 3, 3, 31, 53, 5, 3, 3, 3, 3, 3,
    5, 7, 3, 3, 23, 5, 3, 3380561, 3, 3, 40627, 5,
    3, 67, 337, 3, 3, 3, 5, 29, 3, 3, 5, 3,
    3, 2543, 22441, 3, 11, 3, 24001, 5, 13, 3, 3, 107,
    3, 5, 3, 3, 32003, 13, 3, 3, 3, 11, 7, 5,
    5279, 3, 3, 11, 3, 19913, 3, 587, 31, 384851, 3, 5,
    3, 3, 3, 3, 167, 3, 3, 3, 5, 3, 15583, 3,
    3, 3, 3, 3, 149, 5, 3, 6077507, 11, 17, 3, 5,
    23, 3, 3, 47765093, 3, 3, 5, 3, 3, 1423, 7, 3,
    179, 5, 7, 3, 31, 3, 5, 3, 17, 197, 3, 5,
    3, 263, 3, 5, 673, 3, 13, 3, 3, 7, 3, 5,
    9511, 7, 3, 54623011, 3, 3, 3, 7, 11, 4813, 3, 3,
    433, 13, 3, 3, 8537, 3, 379, 3, 3, 5, 3, 3,
    5, 3, 3, 1782241, 3, 3, 67, 5, 3, 3, 1911263, 5,
    809, 3, 11, 3, 3, 345727, 3, 5, 3, 17, 5, 3,
    3, 7, 3, 2230721, 43, 3, 41, 13, 3, 3, 3, 1289,
    23, 3, 3, 19, 3, 3, 3, 3, 419, 5, 3, 3,
    37, 7, 5, 29401, 3, 61, 11, 71, 3, 7, 725189, 3,
    13, 3, 3, 19, 91081, 3, 5, 3, 3, 1171, 7, 3,
    3, 3911, 7, 13, 3, 3, 7, 5, 541, 3, 23, 3,
    5, 359, 3, 5, 3, 3, 5, 3, 8597, 3, 5, 3,
    5, 3, 7, 3, 67, 3, 3, 3, 7, 5, 3, 139,
    3, 3, 3, 11, 3]

theorem prime_sub_6961 : Nat.Prime (6253262345930828 - 6961) := by
  show Nat.Prime 6253262345923867
  exact p6253262345923867

theorem check_6961 : allC 6253262345930828 6961 P10k ds_6961 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 6253262345930828 is 6961. -/
theorem minGB_6961 : minGB 6253262345930828 = 6961 :=
  minGB_eq_of P10k P10k_complete 6253262345930828 6961 (by norm_num) (by norm_num) prime_sub_6961 ds_6961 check_6961

def ds_7559 : List ℕ := [
    2, 7, 89, 3, 5, 3, 7, 3, 114288107, 439, 3, 3,
    5, 3, 479, 19, 7, 3, 3, 5, 3, 3, 53, 17,
    3, 5, 3, 101, 3, 181, 3, 5, 191, 3, 71, 3,
    3, 3, 19, 2388443, 8951, 3, 5, 3, 13, 3, 3, 3,
    7, 3, 16649, 47, 3, 5, 11, 59, 7, 3, 3, 5,
    3, 17, 3, 5, 3, 463, 3, 3, 167, 3, 7, 326941,
    3, 3, 3, 31, 11, 3, 5, 3, 156766693, 3, 5, 3,
    3, 61781, 29, 3, 5, 3, 619, 7, 3, 5, 3, 23,
    13, 5, 3, 3, 3, 229, 7, 31, 3, 3, 11, 13485847,
    17, 3, 3, 3, 59, 3, 3, 5, 3, 7, 11, 37,
    3, 3, 1777, 5471, 3, 5, 3, 11, 3, 3, 3, 13,
    3, 3, 5, 3, 7, 3, 29, 6448399, 3, 5, 3, 41,
    3, 137, 3, 7, 3, 57771523, 3, 5, 3, 1481, 3, 5,
    3, 41744257, 3, 5, 14083, 144671, 3, 5, 13, 7, 3, 3,
    3, 30109, 5081, 3, 5, 3, 3, 11, 3, 5, 3, 3,
    3, 5, 3, 12409, 37, 7, 3, 3, 3, 5, 3, 83,
    3, 5, 2663347, 7, 3, 3, 73, 4649, 349, 3, 3, 3,
    43, 7, 3, 191, 13, 3, 3, 5, 3, 19, 7, 3,
    3, 5, 13, 277, 3, 3, 163, 3, 71, 3, 263, 1356899,
    3, 5, 3, 3, 3, 5, 3, 7, 3, 29, 31, 5,
    13, 3, 3, 3, 131, 10687, 3, 5, 3, 13159, 3, 5,
    23, 3, 7, 17, 3, 3, 233, 3, 3, 29, 3, 3,
    7, 3, 11, 5, 3, 3330787, 3, 3, 3, 3, 3, 3,
    61, 3, 3, 5, 7, 3, 1217, 3, 3, 5, 3, 19,
    3, 251, 5, 7, 13, 5, 3, 7, 3, 11, 2239, 3,
    3, 264137, 3, 601, 3, 3, 17, 3, 11, 3, 193, 13,
    5, 3, 883, 3, 55487, 5, 3, 17, 3, 3, 5, 3,
    61, 3, 3, 3, 10662433, 37, 3, 11, 3, 7, 3, 26399,
    3, 1033, 3, 3, 3, 23, 53, 3, 17, 67, 3, 3,
    5, 1297, 3, 3, 5, 3, 3, 35910071, 5651, 5, 97, 151,
    3, 5, 19, 13, 3, 3, 661, 3, 3, 5, 3, 1091,
    41, 3, 3, 7, 5, 3, 145963, 3, 5, 11, 3, 37,
    3, 7, 3, 3, 3, 84967, 3, 13, 11, 3, 5, 3,
    3, 34141, 3, 5, 3, 51439, 3, 47, 7, 3, 3, 5,
    3, 409, 3, 23629, 17, 3, 3, 5, 37, 3, 11, 19,
    443, 3, 13, 1675589, 3, 7, 11, 73, 3, 7, 3, 5,
    3, 68156243, 3, 5, 3, 3, 3, 3, 7, 321901, 3, 28151,
    3, 101, 3, 7, 3, 3, 3, 5, 260941, 7, 3, 5,
    3, 5, 3, 179, 3, 3, 15193, 3, 3, 3, 3, 37,
    151, 3, 3, 674249, 11, 3, 5, 3, 727, 3, 29, 7649,
    3, 59, 3, 5, 3, 4570843, 3, 5, 3, 3, 3, 3077159,
    3, 41, 23, 3, 3, 11, 3, 3, 5, 3, 114847, 3,
    3, 61, 11, 3, 3, 3, 17, 5, 3, 23, 3, 3,
    5, 3, 1879, 3, 3, 3, 5, 37, 3, 41, 3, 7,
    59, 5, 3, 1379969, 3, 5, 3, 13, 3, 5, 3, 3,
    5, 31, 3, 7, 19, 3, 3, 67, 3, 37, 5, 3,
    7, 129309823, 11, 3, 3, 7, 3, 3, 1753, 127, 5, 3,
    3, 3, 137, 3, 7, 138102443, 3, 19, 3, 3, 3, 5,
    7, 3, 23, 3, 5, 3, 13, 7, 3, 5, 3, 11,
    31, 3, 3, 241, 3, 11, 3, 3, 17, 5, 307, 13,
    5, 3, 3, 3, 5, 173, 317, 5, 3, 2399, 3, 3,
    41, 3, 25247, 11, 3, 3, 3, 11549, 3, 3, 3, 3,
    7, 3, 13, 83, 3, 3, 3, 4428689, 7, 5, 367, 5,
    3, 3, 83423377, 5, 3, 3, 78307, 3, 4073, 13, 3, 3,
    79, 3, 3, 5, 11, 7, 3, 3, 23, 5, 3, 823,
    11, 3, 3, 227, 3, 7, 3, 3, 3, 2593, 11, 3,
    5, 3, 331, 5, 3, 3, 5, 17, 7, 3, 3, 3,
    3, 29, 67, 3, 5, 3, 13, 3, 3, 3, 5, 3,
    201413, 5, 11, 2221, 3, 19, 149, 7, 3, 23, 3, 5,
    5, 43, 7, 107, 3, 3, 349, 3, 3, 3, 5, 3,
    3, 5, 7, 3, 131, 5, 3, 13291, 7, 3, 3, 5,
    3, 3, 3, 59, 3, 5, 3, 19, 3, 3, 5, 3,
    13, 3, 11, 3, 3, 701, 3, 5, 6047, 3, 5, 3,
    3, 3, 241, 3, 5, 53, 7, 3, 3, 3, 29, 293,
    3, 3, 5, 11, 3, 47, 3, 7, 17, 3, 59, 7,
    3, 5, 37, 3, 5, 430091, 3, 3, 13, 229, 3, 3,
    3, 281, 3, 5, 71, 3, 5, 3, 83, 3, 3, 199,
    11, 3, 13, 3, 3, 5, 3, 3, 3181, 11, 103, 3,
    3, 2713, 23, 3, 5, 7, 19, 11, 3, 3, 412219, 7,
    3, 3, 3, 3, 7127, 3, 3, 3, 3373, 3, 3, 73,
    3, 5, 5, 3, 3, 5, 3, 691, 7, 3, 3, 5,
    557, 3, 3, 3, 7, 11, 3, 3, 3, 2027, 3, 5,
    3, 3, 17, 3, 7, 5, 3, 7, 3, 5, 3, 167887,
    3, 13, 3, 289021, 3, 11, 7, 2659, 3, 3, 4597, 3,
    5, 5134567, 7, 3, 10151, 3, 3, 5, 41, 13, 3, 3,
    5, 191, 311, 3, 3, 3169, 3, 3, 31, 769, 93523, 5,
    17, 3, 5, 3, 3, 11, 43, 3, 5, 3, 3, 17,
    3, 3, 1223, 11, 7, 3, 11867, 3, 3, 5, 3, 19,
    3, 3, 3, 3, 3, 17, 5, 64033, 3, 3, 5, 2161,
    3, 170759, 3, 11, 1613, 13, 3, 5, 4619177, 3]

theorem prime_sub_7559 : Nat.Prime (24925556008175266 - 7559) := by
  show Nat.Prime 24925556008167707
  exact p24925556008167707

theorem check_7559 : allC 24925556008175266 7559 P10k ds_7559 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 24925556008175266 is 7559. -/
theorem minGB_7559 : minGB 24925556008175266 = 7559 :=
  minGB_eq_of P10k P10k_complete 24925556008175266 7559 (by norm_num) (by norm_num) prime_sub_7559 ds_7559 check_7559

def ds_7753 : List ℕ := [
    2, 37, 3, 5, 3, 17, 3, 2333, 3, 3, 29, 5,
    3, 7, 3, 3, 3, 19, 5, 3, 23, 503, 3, 3,
    5, 3, 41453, 3, 41, 3, 5, 3, 3, 43746277, 3, 37,
    5, 329293, 3, 3, 3, 11, 3, 983, 3, 3659, 7, 13,
    3, 211, 3, 3, 1913, 3, 3, 3, 3, 67, 5, 3,
    97, 3, 5, 3, 11, 3, 151, 5, 3, 23, 3, 3,
    5, 37, 7, 3, 3, 5, 3, 53, 3, 7, 3, 271,
    43, 3, 3, 5, 3, 7, 3, 3, 5, 3, 179, 3,
    3, 3, 17, 89, 5, 3, 3, 3, 2237, 5, 3, 3,
    3, 41, 5, 13, 3, 227, 7, 3, 11, 3, 3, 3,
    58453, 7, 3, 3, 13, 3, 11, 3, 5, 461, 23203, 3,
    1321, 5, 3, 13, 3, 5, 3, 3, 1965391, 3, 613, 3,
    17, 3, 4483, 3, 19, 3, 5, 3, 7, 3, 5, 3,
    14869, 3, 5, 3, 3, 3, 5, 3, 3, 3, 373, 5,
    7, 3, 3, 101, 3, 17, 11, 3, 7, 3, 5711, 92363,
    5, 3, 7, 3, 3, 3, 5, 257, 136447, 3, 3067, 3,
    11, 3, 3, 3, 19, 43, 3, 3, 3, 31, 5, 29,
    3, 3, 337, 3, 3, 5441743, 5, 3, 7, 3, 3, 233,
    5, 3, 3, 3, 137, 113, 3, 29, 3, 7, 3, 3,
    5, 3, 23, 131, 7, 3, 37, 3, 541, 3, 3, 3,
    3, 2753, 17, 13, 3, 3, 5, 3, 73, 3, 5, 3,
    3, 89, 3, 3, 241, 5, 3, 5, 157, 3, 3643, 30259,
    3, 11, 3, 3, 7, 3, 124771, 5, 191, 59, 5, 13,
    3, 31, 167, 3, 3, 11, 3, 13, 5, 3, 107, 3,
    67, 3, 3, 3, 3, 3, 7, 3, 17, 3, 3, 5,
    13933, 3, 19, 3, 4093, 5, 3, 11, 3, 17, 3, 3,
    3, 367, 3, 251, 3, 3, 19, 3, 47, 5, 3, 7,
    3, 11, 1187, 103, 3, 3, 1453, 3, 13331, 3, 13, 3,
    7, 3, 23, 5, 11, 3, 3, 7, 3, 3, 19, 5,
    3, 3, 37, 5, 3, 173, 71, 3, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 491, 3, 43, 7, 3, 311, 3,
    3, 2539, 5, 3, 3, 37, 3, 5, 3, 3, 5, 3,
    1063, 3, 641, 5, 19, 3, 7, 3, 3, 5, 3, 727,
    13, 3, 7, 3, 7817, 3, 5, 3, 3, 106536403, 5, 3,
    167, 3, 23, 3, 3, 383, 5, 3, 3, 5, 3, 3,
    3, 5, 3, 3, 11, 3, 3, 3, 17, 3, 3359, 3,
    11, 3, 5, 3, 151, 41, 5, 3581029, 3, 3, 7, 3,
    2179, 3, 29, 3, 169695059, 22807, 5, 3, 3, 3, 5, 3,
    373, 3, 19, 3, 37, 53, 3, 229, 5, 557, 7, 3,
    3, 73, 13, 3, 3, 7, 3, 3259, 3, 30900229, 3, 3,
    113, 3, 5, 3, 31, 3, 6561521, 3, 13, 29, 5, 3,
    7, 3, 3, 47, 5, 3, 61, 7, 3, 17, 3, 5,
    7, 3, 3, 36383, 5, 1811, 3, 3, 8923, 3, 43063, 5,
    3, 19, 3, 5, 13, 7, 3, 3, 73, 3, 43, 3,
    3, 3, 7, 3, 5, 3, 20347, 3, 5, 3, 13, 5,
    3, 3, 439, 3, 3, 16033, 11, 3, 5, 3, 3, 79,
    3, 3, 3, 31, 5, 3, 19, 5, 3, 3, 3, 17,
    5479, 113, 3, 1487, 3, 3, 506479, 3, 7, 5, 7, 3,
    3, 4021, 3, 21592897, 3, 7, 3, 3, 1997467, 3, 11, 3,
    3, 5, 5, 3, 11, 3, 5, 1469509, 3, 3, 3, 3,
    3, 1327, 107, 5, 3, 3, 3, 3, 269, 3, 5, 13,
    3, 71, 3, 3, 587, 149, 5, 3, 13, 5, 11, 7,
    3, 59971, 3, 3, 417947, 5, 7, 3, 3, 3, 3, 3,
    349, 29, 3, 3, 1237, 41, 3, 7, 3, 3, 11, 37,
    3, 7, 53, 3, 3, 3, 13, 17, 3, 3, 11, 3,
    3, 31, 5, 3, 83, 3, 5, 25720157, 7, 3, 3, 17,
    3, 61, 3, 3, 13, 5, 3, 3, 3, 251, 5, 17,
    109, 3, 3, 5, 3, 23, 3, 5, 7, 5, 3, 47,
    3, 3, 3, 3, 694979, 3, 3, 3, 31, 3, 5, 3,
    3, 3, 3, 3, 5, 3850009, 3, 7, 157, 5, 3, 6737,
    13, 3, 3, 37, 3, 3, 7, 3, 3, 17, 5, 3,
    5, 20959, 3361, 3, 32569, 3, 17, 3, 719, 5, 3, 59,
    3, 11, 3, 13, 127, 3, 37, 3, 3, 5, 3, 25659943,
    257, 12109, 3, 11, 3, 3, 3, 347, 5, 7, 3, 3,
    563, 5, 3, 3, 23, 3, 7, 3, 3, 7, 3, 3,
    509, 3, 3, 5, 3, 3, 5, 307, 3, 3, 5, 13,
    47, 3, 7, 3, 3, 11, 3, 7, 3, 13, 617, 3,
    3, 139, 3, 141546061, 5, 3, 13, 5, 3, 3, 3, 311,
    5, 3, 3, 7, 3, 3, 3, 3, 5, 7, 3, 3,
    47, 5, 43, 206009, 3, 5, 23, 5, 3, 11, 7, 3,
    5081, 3, 3, 103, 5, 3, 7, 3, 3, 283, 5, 3,
    3, 5, 13, 5, 3, 3, 1551601, 19, 7, 3, 911, 3,
    67, 12365767, 3, 200201, 3, 3, 7, 3, 11, 3, 1769917, 3,
    113, 3, 4789, 3, 941, 3, 3, 3, 226379, 23059, 3, 5,
    3, 3, 3, 17, 3, 83, 5, 3, 3, 3, 29, 5,
    3, 3, 3, 5, 126013, 3, 5, 59, 3, 3, 3, 3,
    3, 19, 3, 8527, 5, 3, 3, 5, 3, 127, 61, 3,
    5, 11, 3, 3, 3, 5, 3, 7, 13, 3, 857, 3,
    7, 31, 7, 863, 5, 3, 3, 3, 17, 5, 3, 3,
    41, 3, 5, 3, 3, 3, 5, 3, 3, 16052371, 3, 7,
    11, 3, 3, 3, 935113, 7, 3, 35088673, 11, 3, 3, 95087,
    3, 36529, 5, 3, 19, 3, 5, 53, 3, 31]

theorem prime_sub_7753 : Nat.Prime (31284177910528922 - 7753) := by
  show Nat.Prime 31284177910521169
  exact p31284177910521169

theorem check_7753 : allC 31284177910528922 7753 P10k ds_7753 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 31284177910528922 is 7753. -/
theorem minGB_7753 : minGB 31284177910528922 = 7753 :=
  minGB_eq_of P10k P10k_complete 31284177910528922 7753 (by norm_num) (by norm_num) prime_sub_7753 ds_7753 check_7753

def ds_8443 : List ℕ := [
    2, 7, 3, 1013, 3, 3321589, 3, 569, 3, 3, 5, 29,
    3, 17, 3, 3, 3, 5, 31, 3, 7, 6751957, 3, 3,
    11, 3, 19, 3, 53, 3, 1277, 3, 3, 23, 3, 5,
    7, 11, 3, 3, 3, 5, 3, 1904467, 3, 7, 5, 641,
    3, 11, 3, 3, 5, 3, 3, 3, 3, 5, 23, 3,
    7, 3, 103, 3, 43, 3, 5, 37, 3, 17, 3, 3,
    7, 13759, 164609791, 3, 3, 152219, 3, 7, 3, 5, 3, 167,
    31, 3, 3, 10789, 3, 1571, 3, 3, 47, 3, 263, 3,
    3, 3, 13, 5, 195014251, 3, 3, 3, 5, 7, 3, 3,
    3, 5, 1427, 2273, 3, 7, 5, 3, 59, 3, 3, 3,
    5, 19, 3, 3, 5, 3, 145897, 3, 1619, 29, 93407, 3,
    5, 11, 3, 47, 3, 7, 3, 3, 5, 3, 11, 3,
    7, 3, 653, 3, 17, 3, 61, 3, 17471, 3, 29, 3,
    97, 3, 1489, 3, 3, 3, 23, 3, 3, 3, 5, 7,
    182300399, 3, 3, 5, 3, 743, 7, 3, 5, 3, 17, 13,
    11, 3, 2917, 3, 3, 3, 83, 7, 19, 3, 11, 3,
    5, 3, 3, 3, 5, 40939, 3, 3, 3, 5, 3037, 7,
    3, 3, 2483753, 3, 3, 5, 63536933, 3, 13, 3, 3, 5,
    223, 3, 3, 3, 5, 2437, 3, 67, 3, 29, 3, 3,
    37, 3, 66173, 7, 5, 3, 11, 3, 40121437, 3, 3, 3,
    3, 5, 7, 11, 3, 3, 97833739, 3, 41, 3, 2309, 3,
    3, 61, 3, 3, 5, 7, 3, 23, 853, 3, 7, 13,
    3, 19, 3, 3, 2969, 3, 5, 11, 7, 241, 17, 257,
    3, 2459, 5, 3, 3, 5, 3, 5, 26227, 3, 127, 3,
    7, 3, 3, 3, 3, 3, 23, 3, 5, 3, 3, 73,
    13537, 3, 691, 3, 5, 53, 3, 5897, 3, 661, 3, 3,
    3, 13, 3, 7, 3, 3, 31, 3, 5, 1447, 3, 11,
    3, 5, 47, 37100983, 3, 3, 5, 3, 13, 3, 5, 3,
    19, 3, 5, 17, 65147, 3, 3, 5, 3, 3, 5, 23,
    3, 3, 5, 43, 3, 7, 17, 3, 3, 3, 3, 3,
    167, 3, 3, 3, 7, 11, 3, 397, 5, 3, 11, 3,
    3, 5, 37, 3, 3, 7, 3, 6564457, 3, 3, 29, 3,
    617, 3, 5, 7, 42989, 3, 1511, 3, 3, 13, 3, 401,
    7, 3, 5, 3, 877, 3, 59, 3, 3, 5, 17, 3,
    7, 3, 11701, 3, 3, 5, 31, 3, 3, 7, 3, 3,
    3, 7832131, 3, 3, 19, 3, 3, 3, 5, 3, 5, 3,
    13, 3, 23, 3, 335898449, 5, 11, 344251, 3, 3, 83, 3,
    5, 3, 1747, 3, 29, 5, 3546373, 3, 3, 3, 6203, 3,
    31, 3, 13, 3, 757, 5, 3, 5, 7, 23, 157, 3,
    3, 5, 29, 3, 3, 5, 3, 353, 3, 5, 3, 3,
    7, 3, 181, 3, 11, 3, 4587403, 3, 173, 5, 7, 3,
    11, 3, 3, 5, 41, 3, 7, 5, 3, 163, 3, 53,
    17, 3, 3, 5, 19, 7, 3, 3, 1499369, 3, 5, 1857593,
    3, 53529337, 3, 7, 131, 73, 3, 3, 7, 3, 11, 3,
    3, 3, 16253, 3, 89, 3, 7, 3, 13, 3, 37, 107,
    3, 3, 17, 3, 3, 5, 28344401, 3, 10667, 3, 3, 23,
    3, 3, 3, 5, 3023, 3, 5, 11, 3, 3, 3, 19,
    191, 5, 3, 16826993, 3, 3, 47, 3, 31, 73, 5, 3,
    3, 911, 3, 5, 3, 53, 3, 3, 5, 3, 7, 3,
    3, 171804361, 17, 3, 977, 3, 7, 9631, 3, 3, 3, 3,
    3, 13, 5, 203669, 3, 3, 3, 3, 7, 3, 1471, 34580719,
    3, 11, 3, 3, 19, 5, 7, 3, 5, 54396367, 83, 5,
    3, 67, 3, 3, 5, 13, 19, 3, 3, 3, 3, 3,
    132547, 3079, 3, 3, 23879, 11, 3, 1879, 3, 3, 5, 13,
    3, 5, 5, 3, 3, 3, 7, 29, 3, 3, 1657, 3,
    3, 5, 43, 3, 13, 3, 7, 97, 37, 3, 3, 5,
    3, 41, 3, 3, 121267, 239, 3, 3, 3, 5, 23, 7,
    19, 3, 3, 449, 3, 11, 3, 7, 9319, 349, 3, 19,
    3, 3, 3, 3, 5, 3, 3, 3, 7, 3, 17, 3,
    3, 3, 3, 3, 7, 139, 3, 761, 5, 13, 3, 11,
    7, 3, 3, 4243, 3, 3, 118019807, 3, 3, 5, 29023, 3,
    3489041, 47, 33253217, 3, 5, 3, 28129513, 3, 5, 31, 3, 17,
    3, 7, 3, 127, 19, 3, 5, 3, 3, 101, 3, 7,
    13, 29, 3, 5, 3, 3, 3, 5, 7, 11, 3, 3,
    5, 17, 3, 3, 7, 3, 5, 3, 3, 193, 3, 3,
    7, 3, 3, 41, 3, 3, 7, 58549, 3, 3, 547, 23,
    7, 3, 5, 3, 3, 5, 3, 419, 3, 5, 7, 3,
    3, 1021, 3, 5, 13, 3, 3919, 7, 3, 3, 3, 5,
    27767, 3, 3, 5, 3, 3, 3, 3, 1635163, 101, 3, 3,
    5, 11, 7, 5481227, 3, 199, 5, 66347, 3, 5, 17, 3,
    5, 3, 3, 13, 7019, 3, 37, 3, 3, 5, 31, 3,
    3, 13, 179, 132953, 3, 3, 5, 17, 223, 3, 5, 3,
    27552979, 7, 3, 61, 3, 3, 11, 3, 5, 3, 7, 3,
    29, 3, 11, 3, 5, 3, 3, 3, 5, 92859433, 3, 34799873,
    3, 3, 3, 31, 3, 5, 313, 3, 3, 3, 5, 13,
    3, 3, 3, 11, 23, 3, 19, 16370867, 3, 3, 3, 3,
    3, 7, 3, 11, 23, 3, 3, 127, 3, 7, 37, 3,
    41, 73, 3, 3, 3, 7, 3, 13, 5, 3, 451967, 3,
    5, 59, 479, 5, 18713, 3, 3, 3, 1759, 520031, 3, 3,
    11, 3, 7, 3, 3, 3, 43, 3, 3, 7, 3, 5,
    38189, 3, 3, 3, 5, 109, 3, 5, 66067, 3, 3, 659,
    3, 5, 11, 3, 13, 3, 7, 59, 3, 5, 11, 3,
    7, 1277, 3, 3, 3, 3, 3, 3, 23, 2221, 3, 31,
    3, 3, 3, 3, 7, 13, 3, 3, 5, 14977231, 6774541, 3,
    5, 11, 3, 7, 53, 3, 3, 3, 13, 3, 5, 3,
    3, 3, 3, 5, 13, 3, 7, 5, 6373, 3, 5, 3,
    303727, 3, 3, 7, 25453, 3, 19437577, 3, 431, 3, 5, 1591099,
    37, 113, 3, 3, 53, 3, 7, 23, 3, 3, 5]

theorem prime_sub_8443 : Nat.Prime (121005022304007026 - 8443) := by
  show Nat.Prime 121005022303998583
  exact p121005022303998583

theorem check_8443 : allC 121005022304007026 8443 P10k ds_8443 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 121005022304007026 is 8443. -/
theorem minGB_8443 : minGB 121005022304007026 = 8443 :=
  minGB_eq_of P10k P10k_complete 121005022304007026 8443 (by norm_num) (by norm_num) prime_sub_8443 ds_8443 check_8443

def ds_8501 : List ℕ := [
    2, 881, 1069, 3, 7, 3, 27011, 3, 83, 5, 3, 3,
    11, 3, 233, 7, 5, 3, 3, 23, 3, 3, 1993, 5,
    3, 227, 3, 11, 3, 13, 3, 461, 7, 3, 5, 3,
    3, 3, 31, 11, 5, 3, 13, 3, 59, 3, 3, 3,
    376729, 3, 77087561, 5, 3, 1907209, 223, 7, 5, 3, 3, 15881,
    3, 17, 3, 2742521, 3, 22307, 3, 3, 7, 3, 31, 5,
    3, 3, 3, 14369, 5, 3, 19, 3, 5, 3, 7, 3,
    3, 2521, 5, 3, 101, 3, 269, 5, 3, 113, 3, 11,
    5, 83, 3, 3, 3, 7, 2909, 5, 3, 3, 2232859, 43,
    5, 3, 3, 3, 2749, 3, 3, 7, 3, 29, 37, 5,
    3, 3, 10883, 7, 3, 11, 3, 5, 3, 3, 3, 19,
    3, 3, 23, 3, 137, 3, 6301, 5, 3, 29, 3, 4451,
    3, 5, 3, 19, 3, 36013, 3, 2111, 3, 222379, 3, 31,
    3, 5, 3, 191, 6829, 55343, 3, 13, 7, 53, 3, 3,
    3, 32531, 5, 3, 11, 3, 3, 5, 3, 7, 3, 3,
    3, 71, 3, 11, 7, 5, 3, 3, 3, 181, 3, 11,
    3, 129461, 7, 47, 3, 3, 131, 6329, 5, 3, 3, 3,
    5, 73, 3, 13, 5, 3, 3, 53, 3, 6833, 5, 3,
    3, 11, 43, 61, 3, 3, 5, 3, 11, 3, 10337, 5,
    3, 23, 3, 3, 3, 7, 3, 397, 3, 11, 5, 206291,
    7, 3, 3, 3, 29917, 5, 3, 167, 3, 82483, 3, 365413,
    7, 3, 59, 5, 3, 3, 67, 3, 3, 1234439, 3, 3,
    18427, 3, 5, 17, 3, 7, 3, 3, 3, 3, 3, 3,
    79, 3, 3, 211, 11, 3, 113, 3, 3, 719, 3, 443,
    3, 5, 7, 13, 98221, 17473403, 3, 5, 3, 109, 5, 3,
    3, 19, 3, 23, 3, 3, 7, 3, 5, 3, 13, 5,
    97, 3, 11, 3, 5, 7, 3, 5, 3, 3, 13, 3,
    7, 3, 3, 3, 37, 29, 3, 7, 3, 163, 3, 127,
    3, 814127, 3, 3, 3, 13, 5, 3, 17, 5, 3, 3,
    11, 139, 3, 3, 1009, 3, 3, 400739, 5, 84629, 11, 59323657,
    3, 67, 7, 5, 3, 3, 4651, 3, 3, 7, 3, 4549,
    5, 3, 3, 5, 73, 3, 5, 3, 149, 2666039, 3, 7,
    3, 97, 3, 3, 3, 13, 3, 23, 5, 3, 107, 3,
    3, 5, 3, 7, 3, 27751, 3, 9161, 5, 3, 3, 371153,
    3, 5, 3, 61, 13, 3, 3, 141499, 5, 3, 461, 95651,
    5, 3, 155222477, 5, 3, 31, 2790223, 5, 3, 5, 3, 11,
    3, 19, 3, 859, 3, 3, 3, 3, 29, 5, 3, 5,
    3, 19, 3, 47, 3, 3, 3, 139, 7, 5, 3, 71,
    3, 17, 3, 29, 3, 3, 5, 3, 3, 3, 3, 181,
    5, 3, 3, 19139, 5, 3, 7, 3, 5, 3, 11, 7,
    3, 5, 3, 6359, 3, 13, 3, 101, 3, 3, 3, 53,
    3, 307, 5, 3, 3, 17, 3, 3, 7, 3, 19, 3,
    3, 593, 7, 3, 3, 3, 5, 11, 3, 2833, 3, 3,
    13, 3, 5, 3, 3, 3, 17, 1637, 3, 5, 3, 23,
    11, 19, 3, 7, 3, 22446071, 3, 17, 3, 113, 3, 3,
    1789, 7, 3, 18355573, 5, 3, 3, 43, 3, 5, 7, 3,
    83, 13, 5, 3, 3, 5, 3, 3, 23, 5, 13, 3,
    3, 3, 7, 3, 11, 5, 3, 79, 3, 3, 3, 7,
    9431, 3, 5, 3, 233, 3, 7, 5, 3, 17, 3, 89,
    5, 3, 3, 7, 3, 5, 3, 3, 17, 19, 11, 5,
    7, 3, 3, 3, 67, 6247, 7, 13, 3, 265273, 3, 3,
    54575077, 3, 3631, 7, 3, 3, 3, 240518441, 3, 3, 3, 3,
    13, 3, 8447, 5, 3, 3, 3, 7, 5, 151, 101, 43,
    3, 3, 19, 3394051, 3, 3, 23371, 3, 11, 5, 3, 3,
    31, 3, 3, 13, 523, 5, 3, 3, 5, 2926961, 3, 401,
    56983081, 3, 3, 7, 3, 773, 3, 3, 3, 31, 5, 3,
    653, 3, 5, 7, 3, 3, 1301, 17, 5, 3, 3, 3,
    3, 131, 59, 3, 29, 3, 5, 3, 3, 3, 1297, 3,
    43, 7, 25035581, 5, 3, 248752069, 7, 5, 3, 991, 3, 71,
    14753, 7, 17, 5, 3, 3, 13, 3, 3, 3, 75617, 3,
    3, 7, 128113, 3, 184283027, 83, 3, 59, 5, 3, 3, 19,
    3, 3, 3, 13, 3, 23, 3, 5, 3, 3, 11, 3,
    67, 3, 5, 3, 3, 29, 3, 6323, 11, 3, 11081129, 3,
    3, 3, 11, 3, 17, 7, 87034099, 3, 3, 3, 3761, 5,
    3, 3, 59, 23, 3, 5, 3, 109, 17, 3, 563, 5,
    3, 11, 19, 3, 43, 5, 3, 3, 11, 79, 3, 3,
    3, 5, 3, 7, 11, 3, 61, 3, 7, 3, 3, 5527,
    13, 3, 37, 3, 3, 945143, 3, 3, 6079, 868199, 5, 3,
    3, 7243, 5, 3, 7, 42990439, 1087, 5, 3, 3, 7, 5,
    3, 3, 3, 3, 5, 3, 3, 3, 5, 3, 3, 1153,
    3, 31, 7, 3, 3, 47, 3, 7, 5, 3, 3, 167,
    5, 3, 3, 3, 10427, 5, 3, 3, 3, 5, 3, 26221579,
    3, 3, 5, 3, 29, 1109, 3, 5, 3, 3407, 3, 2129,
    3, 25579, 3, 23, 3, 7, 31, 5, 3, 3, 5, 3,
    29, 257, 223, 3, 5, 3, 3, 11, 13, 7, 3, 3,
    79, 19, 5, 3, 3, 43, 3, 3, 5, 11, 5, 390459457,
    17, 3, 7, 3, 3, 111121, 7, 3, 13, 3, 3, 5,
    3, 3, 23, 449, 1051, 3, 2699, 3, 3, 17, 3, 5,
    3, 3, 3, 3, 3, 11, 19417, 41957701, 3, 3, 71, 7,
    3, 5, 3, 1283, 13, 5, 3, 20194789, 17830711, 3, 5, 3,
    3, 421, 19, 5, 3, 3, 29, 3, 3, 71279993, 5, 3,
    359, 3, 3, 504893, 3, 2819, 3, 3, 419, 3, 3, 13,
    3, 3, 31, 43, 7, 5, 17, 34949, 3, 3, 61507, 3,
    80923, 97, 7, 5, 3, 3, 23, 5, 3, 3, 3, 5,
    3, 3, 5, 3, 3, 5, 821, 157, 3, 11, 3, 163,
    7, 18481, 13, 3, 3, 137, 3, 3, 3, 5, 3, 911,
    3, 290351, 7, 3, 3, 227, 3, 11, 3, 53, 3, 3,
    3, 3, 127, 5, 3, 10487, 3, 3, 11, 5, 3, 3,
    1621, 3, 3]

theorem prime_sub_8501 : Nat.Prime (255329126688555994 - 8501) := by
  show Nat.Prime 255329126688547493
  exact p255329126688547493

theorem check_8501 : allC 255329126688555994 8501 P10k ds_8501 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 255329126688555994 is 8501. -/
theorem minGB_8501 : minGB 255329126688555994 = 8501 :=
  minGB_eq_of P10k P10k_complete 255329126688555994 8501 (by norm_num) (by norm_num) prime_sub_8501 ds_8501 check_8501

def ds_8933 : List ℕ := [
    2, 31573, 7, 3, 19333, 3, 5, 3, 2113, 1487, 3, 3,
    29, 3, 5, 13, 3319, 3, 3, 11, 3, 3, 2417, 7,
    3, 101, 3, 5, 3, 2707801, 3, 7, 5, 3, 79, 3,
    3, 3, 5, 7, 87683471, 3, 3710657, 3, 5, 3, 3, 3,
    5, 3, 71, 163, 3, 137, 5, 463, 11, 3, 3, 19,
    3, 177893, 3, 61, 3, 5, 3, 3, 5, 3, 37, 17,
    3, 3, 3, 7, 29, 3, 11, 3, 5189, 3, 131, 3,
    3, 13, 41, 3, 17, 3, 5, 5701, 3, 373229, 3, 127,
    7, 13, 3, 3, 3, 5, 17, 49121, 3, 3, 5, 7,
    11, 3, 3, 3, 5, 3, 3, 59, 3, 5, 246974809, 47,
    3, 3, 5, 23, 3, 964883, 3, 7, 3, 3, 3, 823,
    3, 3, 7, 3, 14341, 3, 5, 20031527, 3, 23, 3, 5,
    3, 233, 3, 5, 3, 11, 3, 97, 3, 5, 3, 13,
    3, 7, 3, 41, 5, 295657763, 3, 7, 5, 43, 3, 3,
    3, 7, 37, 3, 4016141, 3, 3, 23478739, 3, 11, 3, 3,
    3, 7019, 3, 5, 31, 10686917, 3, 3, 3, 2579, 3, 1080073,
    3, 7, 5, 11, 3, 3, 5, 7, 12399253, 3, 3, 3,
    11, 5, 3, 113, 31, 3, 3, 13, 3, 5, 307, 3,
    3, 53731, 5, 23, 3, 3, 61, 3, 5, 3, 7, 15551,
    3, 89, 3, 3, 3, 17, 3, 5, 3, 1091, 43, 23,
    11, 3, 3, 3, 47059459, 7, 3, 53, 3, 17, 3, 7,
    5, 3, 13, 8389, 3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 199, 11, 3, 3596167, 3, 3, 3, 3, 3, 3,
    5, 3, 3, 7, 229, 3, 5, 3, 3, 197, 3, 5,
    3, 17, 691, 5, 397, 14627551, 3, 263, 3, 139, 7, 3,
    3, 5, 3, 13, 3, 3, 5, 3, 919, 3, 7, 47,
    13, 3, 5, 3, 1877459, 8017, 3, 29, 3, 3, 61, 3,
    1313747, 3, 3, 3, 5, 5839, 3, 5, 3, 3931, 3, 5,
    3, 7, 3, 3, 3, 5, 164195641, 3, 19, 23, 3, 3,
    37, 5, 3, 3, 11, 3, 3, 13, 7, 59, 5, 191,
    3, 7, 5, 3559, 3, 3, 5, 3, 3, 43, 3, 13749017,
    13, 3, 3, 11, 31, 3, 7, 3, 419, 47, 3, 5,
    3, 41, 3, 3, 3, 5, 3, 7, 296971, 3, 11, 3,
    3, 239, 3, 19255219, 3, 23, 3, 5, 19, 3, 3, 769,
    3, 7, 3, 5, 11, 3, 3, 7, 179, 3, 5, 7,
    11, 3, 5, 13, 3, 5, 31, 613, 3, 29, 3, 17,
    3, 743, 3, 11, 3, 3, 3, 3, 73, 601, 3, 59,
    3, 5, 3, 5, 3, 3, 3, 19415251, 93407, 97, 3, 1901,
    3, 13, 3, 5, 3, 3, 39408947, 3, 3, 3, 3, 7,
    13, 3, 3, 5, 19, 3, 11, 3, 1409, 3, 5, 709,
    3, 7, 3, 37, 3, 5, 3, 7, 3, 3, 3, 5,
    3, 7, 137, 3, 3, 5, 3, 3, 23, 3, 45863011, 3,
    3, 5, 17, 3, 3, 3, 7, 1283, 3, 5, 3, 3,
    7, 3, 13, 3, 3, 3, 47, 5, 3, 25542967, 3, 5,
    67, 43, 3, 11, 3, 36683, 3, 16729, 3, 103, 3, 3,
    7, 5, 3, 967, 17, 3, 3, 5, 3, 1787, 171317, 3,
    5, 617, 269, 3, 3, 181, 3, 3, 467, 7, 31891417, 3,
    3, 3, 5, 3, 17, 41, 3, 5, 3, 3, 3, 13934497,
    5, 3, 11, 3, 439, 3, 7121, 853, 3, 19, 3, 109,
    7, 3, 3, 5, 3, 37, 3, 3, 7, 29, 5, 23,
    13, 3, 3, 3, 31, 5, 165569, 862913, 3, 11, 3, 3,
    5, 3, 149, 5, 3, 3, 3, 7, 3, 3, 3, 3,
    5, 3, 17, 42719, 3, 3, 3, 113, 227, 11, 61, 2819,
    3, 3, 13, 7, 3, 3, 5, 3, 7, 27457, 3, 3,
    5, 3, 3, 12967, 5, 11, 3, 3, 7, 194267, 3, 5,
    857, 3, 3, 5, 3, 39749, 3, 3, 3, 7, 31, 3,
    11, 3, 443, 17, 3, 3, 353, 5, 23, 3, 3, 3,
    3, 5, 11, 3, 7, 3, 89, 3, 3, 3, 6696779, 3,
    5, 29, 73, 13, 3, 5, 907, 139, 3, 86018201, 3, 11,
    7, 5, 773023, 785423, 3, 3, 5, 3, 3, 3, 647, 3,
    3, 1063, 5, 3, 11, 2957, 3, 5, 103975507, 3, 3, 173,
    3, 3, 3, 431, 3, 7, 3, 19, 3, 3, 23, 3,
    5, 3, 13, 3, 3, 134213, 3, 73, 5, 3, 411703, 3,
    3, 3, 29, 3, 7, 5, 11, 3, 3, 3, 7, 4951,
    3, 3, 41, 5, 3, 11, 3, 5, 13, 3, 5, 31,
    3, 13, 5, 3, 7, 113, 3, 3, 5, 7, 3, 3,
    3, 249763, 3, 179, 16468799, 3, 29, 3, 11, 3, 3, 17,
    5, 3, 23, 3, 3, 7, 3, 3, 5, 7, 387216457, 3,
    3, 5, 47, 3, 31, 5, 19, 683, 3, 3, 41, 362281,
    3, 3, 3, 3, 7, 3, 3, 3, 13, 3, 3, 7,
    3, 5087, 4067411, 3, 3, 19, 3, 4139, 37, 3, 3, 17,
    7, 3, 3, 3, 29, 43, 3, 3, 3, 3001, 3, 97,
    3, 3, 131, 3, 5, 13, 3, 19, 3, 37, 3, 11,
    3, 5, 3, 563, 3, 5, 47, 11, 3, 3, 61, 3,
    137874713, 5, 5, 3, 569, 3, 3, 103, 5, 1873, 3, 3,
    11, 37, 7, 3, 3, 4253, 3, 3, 449, 7, 355541, 19,
    5, 3, 13, 3, 3, 5, 17, 3, 35729, 3, 3, 7,
    3, 3, 5, 541, 97, 3, 5, 3, 3, 11, 3, 19,
    3, 3, 3, 3, 3, 43, 1553, 5, 3, 3, 7, 5,
    3, 17, 3, 5, 7, 11, 3, 13, 5, 3, 13523, 3,
    3, 5, 23, 103, 3, 3, 5, 3, 3, 9241, 7, 3,
    797, 3, 3, 7, 3, 17, 3, 3, 5, 3, 3, 5,
    3, 3, 11, 5, 67, 41, 761, 13, 3, 3, 5, 3,
    10687, 7, 5, 19, 3, 3, 5, 43, 3, 3, 3, 13,
    3, 3, 1091, 3, 3, 7, 256639, 5, 3, 70981, 3, 7,
    5, 11, 5, 3, 3, 31, 3, 3, 3, 29, 3, 311,
    3, 5, 13, 3, 3, 23, 3, 131, 3, 5, 3, 3,
    3, 3, 7, 76337629, 3, 5, 3, 3, 2237, 59, 3, 3,
    5, 3, 3, 4721, 387884521, 3, 3, 5, 3, 31, 3, 7,
    3, 5, 3, 68521, 3, 5, 3, 3, 3, 379, 367, 3,
    79, 3, 229, 7, 3, 3, 3, 3, 3, 7, 5, 71,
    3, 3, 7, 3, 5, 252151, 3, 19, 5, 3, 11, 109,
    3, 5, 3, 3, 3, 3]

theorem prime_sub_8933 : Nat.Prime (258549426916149682 - 8933) := by
  show Nat.Prime 258549426916140749
  exact p258549426916140749

theorem check_8933 : allC 258549426916149682 8933 P10k ds_8933 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 258549426916149682 is 8933. -/
theorem minGB_8933 : minGB 258549426916149682 = 8933 :=
  minGB_eq_of P10k P10k_complete 258549426916149682 8933 (by norm_num) (by norm_num) prime_sub_8933 ds_8933 check_8933

def ds_8941 : List ℕ := [
    2, 7, 3, 5, 3, 73, 3, 19, 3, 3, 7, 5,
    3, 53, 3, 3, 3, 13, 5, 3, 7, 41, 3, 3,
    5, 3, 157, 3, 43, 3, 5, 3, 3, 11, 3, 991,
    5, 37, 3, 3, 3, 4391, 3, 29, 3, 7, 23143343, 1049,
    3, 61, 3, 3, 7, 3, 3, 3, 3, 11, 5, 3,
    7, 3, 5, 3, 59, 3, 263, 5, 3, 497011, 3, 3,
    5, 13, 1373, 3, 3, 5, 3, 7, 3, 181, 3, 83,
    2059339, 3, 3, 5, 3, 359, 3, 3, 5, 3, 1697, 3,
    3, 3, 563, 29, 5, 3, 3, 3, 41, 5, 3, 3,
    3, 11, 5, 271, 3, 7, 31, 3, 109, 3, 3, 3,
    7, 97, 3, 3, 322613, 3, 641959, 3, 5, 11, 952681, 3,
    17, 5, 3, 142837, 3, 5, 3, 3, 285644939, 3, 266159, 3,
    7, 3, 17, 3, 683, 3, 5, 3, 43, 3, 5, 3,
    13, 3, 5, 3, 3, 3, 5, 3, 3, 3, 197, 5,
    769, 3, 3, 59, 3, 419, 7, 3, 37, 3, 11, 593817863,
    5, 3, 71, 3, 3, 3, 5, 7, 11, 3, 13, 3,
    7833769, 3, 3, 3, 23, 919, 3, 3, 3, 13, 5, 7,
    3, 3, 425560829, 3, 3, 7, 5, 3, 107, 3, 3, 79,
    5, 3, 3, 3, 251, 43, 3, 229, 3, 83, 3, 3,
    5, 3, 67, 7, 534253, 3, 21881, 3, 21056501, 3, 3, 3,
    3, 1126031, 7, 401, 3, 3, 5, 3, 13217, 3, 5, 3,
    3, 647, 3, 3, 13, 5, 3, 5, 137, 3, 7, 61,
    3, 13, 3, 3, 11, 3, 891047, 5, 7, 29, 5, 457,
    3, 11, 41, 3, 3, 1174361, 3, 1583, 5, 3, 17, 3,
    7, 3, 3, 3, 3, 3, 13, 3, 53, 3, 3, 5,
    3331, 3, 44269, 3, 13, 5, 3, 23, 3, 11, 3, 3,
    3, 59, 3, 7, 3, 3, 113, 3, 7, 5, 3, 12689,
    3, 37, 17, 73, 3, 3, 67129, 3, 271, 3, 11, 3,
    53, 3, 17, 5, 41, 3, 3, 313, 3, 3, 7, 5,
    3, 3, 47, 5, 3, 7, 541, 3, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 65839, 3, 175991, 12541, 3, 41, 3,
    3, 7, 5, 3, 3, 7, 3, 5, 3, 3, 5, 3,
    67, 3, 1229903, 5, 109786909, 3, 17, 3, 3, 5, 3, 11,
    7, 3, 1056481, 3, 1201, 3, 5, 3, 3, 13, 5, 3,
    7, 3, 183683, 3, 3, 33893, 5, 3, 3, 5, 3, 3,
    3, 5, 3, 3, 211, 3, 3, 3, 7, 3, 97, 3,
    101, 3, 5, 3, 31, 67, 5, 73, 3, 3, 11, 3,
    733, 3, 2039, 3, 10977539, 7, 5, 3, 3, 3, 5, 3,
    107, 3, 409, 3, 13, 23, 3, 17, 5, 14461, 522829, 3,
    3, 1973, 725281463, 3, 3, 233, 3, 11, 3, 7, 3, 3,
    7, 3, 5, 3, 43, 3, 113, 3, 29, 7393, 5, 3,
    470437717, 3, 3, 53, 5, 3, 7, 11, 3, 97, 3, 5,
    1831, 3, 3, 227, 5, 7, 3, 3, 29, 3, 79, 5,
    3, 17, 3, 5, 4943, 139, 3, 3, 7, 3, 31, 3,
    3, 3, 23, 3, 5, 3, 7, 3, 5, 3, 61, 5,
    3, 3, 83, 3, 3, 2563901, 245257, 3, 5, 3, 3, 55799,
    3, 3, 3, 7, 5, 3, 47389, 5, 3, 3, 3, 50607617,
    11, 283, 3, 137, 3, 3, 83833, 3, 37, 5, 929, 3,
    3, 17, 3, 7, 3, 231419, 3, 3, 41, 3, 7, 3,
    3, 5, 5, 3, 757, 3, 5, 11, 3, 3, 3, 3,
    3, 17, 7, 5, 3, 3, 3, 3, 7, 3, 5, 23,
    3, 633271, 3, 3, 59771, 11, 5, 3, 599, 5, 37, 61,
    3, 79, 3, 3, 7, 5, 13, 3, 3, 3, 3, 3,
    31, 17, 3, 3, 11, 383171, 3, 23, 3, 3, 21977, 53,
    3, 17, 7, 3, 3, 3, 7, 31, 3, 3, 17, 3,
    3, 137, 5, 3, 83477, 3, 5, 227, 41, 3, 3, 43,
    3, 11, 3, 3, 120671, 5, 3, 3, 3, 10346459, 5, 7,
    367, 3, 3, 5, 3, 307, 3, 5, 13, 5, 3, 4104421,
    3, 3, 3, 3, 7, 3, 3, 3, 7, 3, 5, 3,
    3, 3, 3, 3, 5, 29, 3, 11, 1783, 5, 3, 13,
    7, 3, 3, 23, 3, 3, 113, 3, 3, 13, 5, 3,
    5, 40193, 167, 3, 1571, 3, 59, 3, 5393, 5, 3, 31,
    3, 7, 3, 11, 47384867, 3, 7, 3, 3, 5, 3, 7,
    11, 71, 3, 2260633, 3, 3, 3, 281, 5, 31, 3, 3,
    17, 5, 3, 3, 7, 3, 11, 3, 3, 239, 3, 3,
    7, 3, 3, 5, 3, 3, 5, 43, 3, 3, 5, 1004477,
    7, 3, 32563, 3, 3, 7, 3, 677, 3, 353, 7, 3,
    3, 27385543, 3, 11, 5, 3, 41, 5, 3, 3, 3, 170454247,
    5, 3, 3, 13, 3, 3, 3, 3, 5, 11, 3, 3,
    17, 5, 7, 13, 3, 5, 179, 5, 3, 61, 145257083, 3,
    1009321, 3, 3, 109, 5, 3, 3671, 3, 3, 167, 5, 3,
    3, 5, 197107931, 5, 3, 3, 1301, 11, 67, 3, 13, 3,
    131, 7, 3, 72467, 3, 3, 4219, 3, 1637, 3, 7, 3,
    37, 3, 1507379, 3, 32987, 3, 3, 3, 11, 47, 3, 5,
    3, 3, 3, 86892131, 3, 7, 5, 3, 3, 3, 3167, 5,
    3, 3, 3, 5, 53, 3, 5, 11, 3, 3, 3, 3,
    3, 7, 3, 13, 5, 3, 3, 5, 3, 7, 294157, 3,
    5, 1471, 3, 3, 3, 5, 3, 1747, 367, 3, 11, 3,
    593, 619, 13, 23, 5, 3, 3, 3, 41, 5, 3, 3,
    37, 3, 5, 3, 3, 3, 5, 3, 3, 7, 3, 119389,
    167, 3, 3, 3, 7, 193, 3, 117004141, 157, 3, 3, 2203,
    3, 47279, 5, 3, 31, 3, 5, 107, 3, 103, 42901, 3,
    7, 17, 3, 3, 3, 3, 3, 3, 5, 2161, 3, 8009,
    3, 3, 3, 3, 5, 37, 3, 3, 41, 23, 11, 3,
    7, 5, 3, 7, 11, 3, 3, 3, 1987, 3, 23, 3,
    3, 3, 3, 163, 5, 3, 7, 11, 433, 3, 7, 3,
    5039467, 3, 3, 7, 353, 3, 5, 3, 47, 3, 53, 5,
    13, 16111, 3, 3, 5, 3, 7, 199, 3, 3, 7, 31,
    3, 587, 5, 3, 3, 11, 5, 3, 44895143, 3, 13, 3,
    157, 3, 7, 3, 43, 3, 31, 7, 5, 3, 3, 5,
    3, 41, 3, 3, 5, 928903, 11, 176181079, 5, 3, 3, 3,
    71, 28151, 3, 604369, 3, 3, 37, 3, 3, 5760277, 3, 3,
    307, 3, 5, 7, 954697, 23, 3]

theorem prime_sub_8941 : Nat.Prime (555274351556750822 - 8941) := by
  show Nat.Prime 555274351556741881
  exact p555274351556741881

theorem check_8941 : allC 555274351556750822 8941 P10k ds_8941 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 555274351556750822 is 8941. -/
theorem minGB_8941 : minGB 555274351556750822 = 8941 :=
  minGB_eq_of P10k P10k_complete 555274351556750822 8941 (by norm_num) (by norm_num) prime_sub_8941 ds_8941 check_8941

def ds_9161 : List ℕ := [
    2, 5, 7589, 3, 7, 3, 23, 3, 5, 383, 3, 3,
    62844367, 3, 906931, 5, 11, 3, 3, 271, 3, 3, 5, 1669,
    3, 13, 3, 397, 3, 5, 3, 73, 7, 3, 19207, 3,
    3, 3, 71, 5, 7, 3, 11, 3, 29, 3, 3, 3,
    1916753, 3, 5, 59, 3, 151799, 11, 5, 813647, 3, 3, 5104973,
    3, 5, 3, 1549, 3, 2903, 3, 3, 7, 3, 5, 2017,
    3, 3, 3, 5, 7, 3, 9091, 3, 43, 3, 7, 3,
    3, 5, 7331, 3, 569, 3, 443, 61, 3, 13, 3, 5,
    17, 11, 3, 3, 3, 7, 5, 13, 3, 3, 11, 5,
    7, 3, 3, 3, 31, 3, 3, 7, 3, 13, 5, 1200359,
    3, 3, 43, 5, 3, 10993, 3, 11, 3, 3, 3, 5,
    3, 3, 278382959, 3, 5, 3, 59671, 7, 3, 47, 3, 193,
    3, 57347, 3, 37, 3, 5, 3, 13, 3, 1013, 3, 2785187,
    3, 16417, 3, 170101, 59, 5, 3, 14369, 7, 5, 3, 3,
    3, 5, 7, 3, 83, 3, 3, 11, 3, 7, 3, 3,
    3, 19, 3, 101, 5, 809, 3, 3, 3, 521, 3, 5,
    3, 11, 7, 5, 3, 3, 53, 5, 7, 3, 3, 3,
    23, 631, 3, 5, 127, 3, 3, 37, 3, 41, 19, 3,
    3, 31, 2837, 5, 3, 3, 947, 3, 13, 3, 5, 7,
    3, 43, 3, 3, 3, 7, 3, 241564357, 3, 5, 827, 11,
    5, 3, 3, 3, 5, 79, 3, 331, 3, 5, 3, 2039,
    7, 3, 5, 6247, 3, 3, 16149629, 3, 3, 47, 3, 3,
    271, 3, 11, 1213, 3, 5, 3, 3, 3, 3, 3, 3,
    9649, 3, 3, 23, 5, 3, 931123, 3, 3, 71, 3, 67723,
    3, 19, 7, 11, 5, 68503181, 3, 23, 3, 5, 6761, 3,
    3, 53407, 3, 5, 3, 3, 7, 3, 11, 3, 5, 7,
    6709, 3, 23, 3, 157, 7, 3, 13, 3, 3, 17, 3,
    5, 3, 3, 3, 13, 5, 3, 7, 3, 5, 3, 647,
    3, 5, 3, 3, 3, 71, 61, 3, 5, 227, 3, 3,
    7723, 92158879, 3, 3, 7471249, 3, 3, 5, 36067, 37, 89273, 5,
    3, 13, 7, 19, 3, 3, 31, 3, 3, 7, 3, 5,
    17, 3, 3, 12211, 1893643, 3, 733, 3, 5351, 5, 3, 7,
    3, 5, 3, 3, 3, 19, 3, 5, 7, 3, 3510179, 3,
    3, 1021, 3, 7, 3, 5, 3, 23, 1867, 3, 3, 19,
    3, 4271, 3, 51590167, 5, 3, 3, 137, 419, 3, 11, 5,
    7, 3, 547, 173, 3, 17, 5, 97, 3, 43, 3, 691,
    3, 5, 3, 61, 3, 3, 3, 3, 5, 1697, 3, 7,
    3, 16815859, 3, 1181, 3, 3, 3, 23, 5, 40530331, 3, 13,
    3, 1471, 3, 19, 3, 3, 13, 3, 3, 3, 3, 5,
    7, 3, 3, 59341, 11, 3, 7, 3, 13901, 3, 31, 5,
    3, 467, 3, 879247, 3, 17, 3, 11, 3, 3, 3, 251,
    3, 5, 7, 3, 3, 11, 3, 3, 7, 3, 5, 3,
    3, 179, 5, 3, 3, 3, 3209, 17, 3, 29, 3, 3,
    227, 3, 1601, 3, 3, 3, 53, 13, 3, 31, 3, 317,
    5, 11, 3, 5, 3, 29, 3, 5, 3, 23, 3, 3,
    239412337, 7, 3, 5, 79, 3, 3, 219277, 3, 29959, 7, 3,
    487, 5, 11, 3, 3, 163, 3, 3, 5, 13, 131, 3,
    3, 3, 7, 3, 5, 61, 3, 13, 3, 3, 3, 7,
    11, 3, 149, 3, 8443, 3, 5, 41, 3, 1050473, 3, 5,
    43, 3, 3, 7, 3, 11, 3, 3, 5, 13, 19, 37,
    7, 3, 3, 3, 16958831, 2269, 5, 11, 3, 5, 3, 3,
    83, 3, 5, 7, 3, 3, 3, 5, 3, 3, 3, 3,
    67, 3, 5, 373, 3, 3, 3, 5, 11, 17, 5, 29,
    3, 3, 5, 41, 3, 3, 502121, 3, 5, 7, 3, 3,
    37511, 3, 3, 61, 11, 22541, 3, 3, 42899, 3581, 3, 13,
    5, 3, 3, 7, 3, 5, 3, 3, 3, 5, 7, 3,
    37889, 3, 67, 7, 3, 3, 19, 151, 17, 3, 3, 3,
    3, 28433, 5, 3, 13, 3, 2399, 3, 3, 3, 109, 3,
    61, 7, 5, 71, 3, 37, 5, 19, 3, 5, 3, 53,
    134218423, 7, 5, 23, 3, 3, 29, 3, 3, 3, 67, 3,
    3, 7, 22291, 3, 5, 5172163, 3, 17, 37, 3, 3, 58727,
    3, 3, 3, 5, 3, 29, 3, 7, 3, 3, 19, 3,
    1053421, 3, 11, 3, 3, 5, 3, 17, 13, 3, 37, 3,
    3, 3, 5, 3, 11, 7, 5, 3, 3, 3, 5, 7,
    3, 3, 127, 11, 3, 19, 3, 47, 5, 3, 1657, 29,
    3, 41, 53, 3, 31, 13, 3, 3, 10751483, 5, 3, 3,
    3, 23, 3, 7, 5, 3, 11, 3, 5, 3, 3, 5,
    11, 3, 5, 3, 3, 17, 3, 3, 59, 5, 7, 3,
    3, 29, 79, 3, 7, 719, 5, 11, 3, 3, 5, 401,
    3, 3, 3, 3, 1291, 3, 3, 3, 19, 3, 3, 5,
    3, 653, 7, 3, 3, 101, 3, 5, 31, 3, 3, 367,
    103, 3, 3, 3, 5, 11, 3, 3, 3, 7, 3, 61,
    3, 3, 41, 3, 1637, 557, 3, 23, 3, 11, 3, 5,
    3, 2557, 3, 5, 3, 7, 5, 43, 3, 3, 7, 3,
    149, 23, 95419, 3, 67789, 3, 3, 137, 859, 5, 3, 3,
    9733, 5, 19, 3, 3, 5, 3, 3, 1811, 5, 7, 11,
    31, 3, 7, 3, 3, 11, 5, 3, 41, 3, 3, 2125229,
    3, 3, 19, 5, 5, 3, 47, 3, 3, 23, 3, 24874067,
    3, 3, 3, 3, 3, 5, 11, 41, 3, 3, 56731, 7,
    3, 31, 3, 11, 5, 7, 3, 13709, 17, 3, 281, 3,
    3, 53, 5, 13, 3, 3, 23, 3, 3, 5, 11, 3,
    5, 3, 3, 60811, 3, 5, 3, 3, 134371, 3, 3, 1747,
    3, 3, 5, 19, 5, 7069, 252979, 5, 3, 3, 890889877, 3,
    5, 13, 7, 5483, 3, 3, 6977, 7, 3, 3, 3, 2371,
    3, 3, 223, 3, 3, 2087, 929, 107, 3, 5, 3, 11,
    7, 5, 127, 3, 3, 24793, 3, 3, 3, 7664369, 3, 607,
    3, 543259, 5, 3, 3, 5, 3, 13, 3, 23, 3, 3,
    3, 3, 5, 7, 3, 19, 3, 3, 5, 31, 3, 3,
    13, 3, 3, 19, 5, 3, 3, 7, 3, 5, 3, 5,
    3, 12453653, 3, 104179, 3, 37, 3, 3, 3, 5, 17, 3,
    13, 3, 5, 149, 3, 3, 3, 3, 3, 877, 7, 5,
    3, 3, 5, 3, 131, 1721, 3, 7, 11, 3, 23, 95713,
    3, 4621, 3, 3, 3, 3, 5, 3, 369499499, 5, 11, 3,
    7, 3, 3, 1548593, 3, 3041, 7, 3, 3, 67, 3, 3,
    3, 3, 3, 3, 1663, 3, 3]

theorem prime_sub_9161 : Nat.Prime (887123803077837868 - 9161) := by
  show Nat.Prime 887123803077828707
  exact p887123803077828707

theorem check_9161 : allC 887123803077837868 9161 P10k ds_9161 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 887123803077837868 is 9161. -/
theorem minGB_9161 : minGB 887123803077837868 = 9161 :=
  minGB_eq_of P10k P10k_complete 887123803077837868 9161 (by norm_num) (by norm_num) prime_sub_9161 ds_9161 check_9161

def ds_9341 : List ℕ := [
    2, 13, 383, 3, 151, 3, 5, 3, 7, 13, 3, 3,
    191, 3, 5, 11, 31, 3, 3, 109, 3, 3, 167, 859,
    3, 17, 3, 5, 3, 1105261, 3, 73, 5, 3, 7, 3,
    3, 3, 5, 419, 19, 3, 7, 3, 5, 3, 3, 3,
    5, 3, 7, 27749, 3, 11, 5, 13, 71, 3, 3, 28843,
    3, 19, 3, 1381, 3, 5, 3, 3, 5, 3, 23, 7,
    3, 3, 3, 11, 257, 3, 7, 3, 13, 3, 31, 3,
    3, 7, 11, 3, 359, 3, 5, 1223, 3, 23, 3, 5189,
    17, 19, 3, 3, 3, 5, 227, 7, 3, 3, 5, 37,
    59, 3, 3, 3, 5, 3, 3, 9431, 3, 5, 7, 109639,
    3, 3, 5, 449, 3, 53, 3, 47, 3, 3, 3, 103,
    3, 3, 65447, 3, 149, 3, 5, 13, 3, 7, 3, 5,
    3, 1405333, 3, 5, 3, 7, 3, 36264577, 3, 5, 3, 11,
    3, 349, 3, 137, 5, 59, 3, 43, 5, 4567, 3, 3,
    3, 1609, 17, 3, 7, 3, 3, 212437, 3, 293, 3, 3,
    3, 19, 3, 5, 1993, 11, 3, 3, 3, 1693, 3, 2129951,
    3, 23, 5, 607, 3, 3, 5, 17, 43, 3, 3, 3,
    37, 5, 3, 7, 1347569, 3, 3, 127, 3, 5, 19, 3,
    3, 31, 5, 11, 3, 3, 7, 3, 5, 3, 13, 11,
    3, 7, 3, 3, 3, 37, 3, 5, 3, 7, 1188977, 13,
    89, 3, 3, 3, 2239, 181, 3, 11, 3, 67, 3, 19022741,
    5, 3, 132353189, 7, 3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 347, 1307, 3, 17, 3, 3, 3, 3, 3, 3,
    5, 3, 3, 491, 13, 3, 5, 3, 3, 7, 3, 5,
    3, 19, 11, 5, 7, 257, 3, 7717, 3, 53, 13, 3,
    3, 5, 3, 19, 3, 3, 5, 3, 7, 3, 127, 1193,
    7, 3, 5, 3, 11, 26188493, 3, 47, 3, 3, 17, 3,
    107, 3, 3, 3, 5, 13, 3, 5, 3, 17, 3, 5,
    3, 546599, 3, 3, 3, 5, 683666779, 3, 7, 1487, 3, 3,
    179, 5, 3, 3, 1133789, 3, 3, 6553, 71, 47, 5, 23,
    3, 577, 5, 7, 3, 3, 5, 3, 3, 1423, 3, 7,
    17, 3, 3, 60610441, 37, 3, 53, 3, 90227, 20430827, 3, 5,
    3, 29, 3, 3, 3, 5, 3, 11, 23, 3, 7, 3,
    3, 151, 3, 16171061, 3, 7, 3, 5, 67, 3, 3, 19,
    3, 97, 3, 5, 2011, 3, 3, 46063783, 7, 3, 5, 79,
    47533, 3, 5, 251, 3, 5, 7, 1301, 3, 743, 3, 29,
    3, 11, 3, 11617, 3, 3, 3, 3, 83, 7, 3, 719,
    3, 5, 3, 5, 3, 3, 3, 67, 139, 3343, 3, 11,
    3, 23, 3, 5, 3, 3, 7, 3, 3, 3, 3, 16137941,
    30937, 3, 3, 5, 29, 3, 19, 3, 23, 3, 5, 147449,
    3, 653, 3, 13, 3, 5, 3, 1063001, 3, 3, 3, 5,
    3, 29, 13, 3, 3, 5, 3, 3, 83, 3, 7, 3,
    3, 5, 523, 3, 3, 3, 89, 17, 3, 5, 3, 3,
    37, 3, 7, 3, 3, 3, 7, 5, 3, 31, 3, 5,
    7, 47, 3, 103, 3, 13, 3, 6148853, 3, 11, 3, 3,
    41, 5, 3, 37, 7, 3, 3, 5, 3, 173, 62187599, 3,
    5, 7, 61, 3, 3, 101, 3, 3, 73, 11, 167, 3,
    3, 3, 5, 3, 2862589, 7, 3, 5, 3, 3, 3, 11,
    5, 3, 29, 3, 13, 3, 53861, 353, 3, 6798937, 3, 17,
    25253, 3, 3, 5, 3, 7, 3, 3, 401, 7, 5, 11,
    201301699, 3, 3, 3, 103, 5, 51282337, 997, 3, 23, 3, 3,
    5, 3, 31, 5, 3, 3, 3, 43, 3, 3, 3, 3,
    5, 3, 7, 41, 3, 3, 3, 11, 18443, 17, 271, 107,
    3, 3, 5701, 29, 3, 3, 5, 3, 17, 67, 3, 3,
    5, 3, 3, 11, 5, 1549, 3, 3, 3169, 5387, 3, 5,
    13, 3, 3, 5, 3, 12553, 3, 3, 3, 11, 1049, 3,
    7, 3, 157, 137, 3, 3, 19, 5, 13, 3, 3, 3,
    3, 5, 53, 3, 197, 3, 7, 3, 3, 3, 7, 3,
    5, 89, 7, 22717, 3, 5, 17, 19, 3, 11, 3, 153086831,
    71, 5, 313, 7, 3, 3, 5, 3, 3, 3, 7, 3,
    3, 53, 5, 3, 7, 61381, 3, 5, 2071591, 3, 3, 11,
    3, 3, 3, 83, 3, 257351, 3, 31, 3, 3, 7, 3,
    5, 3, 490937, 3, 3, 7, 3, 17, 5, 3, 131129, 3,
    3, 3, 8737, 3, 13, 5, 17, 3, 3, 3, 433, 61,
    3, 3, 7, 5, 3, 13, 3, 5, 7, 3, 5, 7517,
    3, 157, 5, 3, 23, 7, 3, 3, 5, 839, 3, 3,
    3, 14401, 3, 3923, 7, 3, 43, 3, 29, 3, 3, 637379,
    5, 3, 239, 3, 3, 17, 3, 3, 5, 59, 13, 3,
    3, 5, 3769, 3, 97, 5, 7, 89, 3, 3, 151, 47,
    3, 3, 3, 3, 11, 3, 3, 3, 7, 3, 3, 101,
    3, 7, 11, 3, 3, 2411, 3, 19, 31, 3, 3, 13,
    443227, 3, 3, 3, 11, 7, 3, 3, 3, 77573, 3, 7,
    3, 3, 11, 3, 5, 523, 3, 401, 3, 19, 3, 18353,
    3, 5, 3, 17, 3, 5, 41, 7, 3, 3, 383, 3,
    7, 5, 5, 3, 112979, 3, 3, 13, 5, 11, 3, 3,
    397, 29, 19, 3, 3, 18285413, 3, 3, 7, 173, 41, 7,
    5, 3, 401053, 3, 3, 5, 620657, 3, 67, 3, 3, 4729,
    3, 3, 5, 23, 13, 3, 5, 3, 3, 7, 3, 70583,
    3, 3, 3, 3, 3, 719, 4019, 5, 3, 3, 6793, 5,
    3, 7, 3, 5, 12557483, 23, 3, 7, 5, 3, 6883, 3,
    3, 5, 7, 19, 3, 3, 5, 3, 3, 11, 17, 3,
    13, 3, 3, 25261, 3, 19, 3, 3, 5, 3, 3, 5,
    3, 3, 7, 5, 1115561, 13, 11, 17, 3, 3, 5, 3,
    29, 1669, 5, 7, 3, 3, 5, 236771, 3, 3, 3, 3697,
    3, 3, 11, 3, 3, 358811, 23, 5, 3, 41, 3, 281,
    5, 256469, 5, 3, 3, 7, 3, 3, 3, 13, 3, 29,
    3, 5, 31, 3, 3, 19, 3, 101, 3, 5, 3, 3,
    3, 3, 17, 11, 3, 5, 3, 3, 7, 31, 3, 3,
    5, 3, 3, 11, 5279, 3, 3, 5, 3, 877, 3, 107,
    3, 5, 3, 13, 3, 5, 3, 3, 3, 8117, 17, 3,
    751, 3, 229, 11, 3, 3, 3, 3, 3, 59, 5, 29,
    3, 3, 13003, 3, 5, 67, 3, 11, 5, 3, 226547, 4937,
    3, 5, 3, 3, 3, 3, 317, 3, 12659623, 11, 7, 3,
    13, 3, 3, 7, 3, 11, 139, 3, 3, 83, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 11, 31, 3, 3, 3,
    15391, 191, 7, 5, 44187733, 3, 5, 3, 17, 3, 11, 13,
    3, 23, 3]

theorem prime_sub_9341 : Nat.Prime (906030579562279642 - 9341) := by
  show Nat.Prime 906030579562270301
  exact p906030579562270301

theorem check_9341 : allC 906030579562279642 9341 P10k ds_9341 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 906030579562279642 is 9341. -/
theorem minGB_9341 : minGB 906030579562279642 = 9341 :=
  minGB_eq_of P10k P10k_complete 906030579562279642 9341 (by norm_num) (by norm_num) prime_sub_9341 ds_9341 check_9341

def ds_9629 : List ℕ := [
    2, 5, 4483, 3, 43, 3, 23, 3, 5, 583459, 3, 3,
    7, 3, 76403, 5, 1229953499, 3, 3, 22093, 3, 3, 5, 1283,
    3, 19, 3, 375931, 3, 5, 3, 11, 601, 3, 131, 3,
    3, 3, 7, 5, 149, 3, 1319, 3, 11, 3, 3, 3,
    17, 3, 5, 480527, 3, 7, 821, 5, 43, 3, 3, 2126269,
    3, 5, 3, 1523, 3, 252778121, 3, 3, 37, 3, 5, 1030537,
    3, 3, 3, 5, 27324461, 3, 173, 3, 7, 3, 13, 3,
    3, 5, 103, 3, 7, 3, 283, 65726651, 3, 193, 3, 5,
    13, 34381, 3, 3, 3, 19, 5, 23, 3, 3, 7, 5,
    31, 3, 3, 3, 42649, 3, 3, 7451, 3, 97, 5, 11,
    3, 3, 59, 5, 3, 940864423, 3, 6661, 3, 3, 3, 5,
    3, 3, 89, 3, 5, 3, 7, 29, 3, 13, 3, 8933,
    3, 7, 3, 11, 3, 5, 3, 7, 3, 229, 3, 1049,
    3, 4597, 3, 17, 2729, 5, 3, 31, 13, 5, 3, 3,
    3, 5, 1303, 3, 59, 3, 3, 7, 3, 14390333, 3, 3,
    3, 7, 3, 17117, 5, 172307, 3, 3, 3, 6547, 3, 5,
    3, 541, 11, 5, 3, 3, 7, 5, 97, 3, 3, 3,
    7, 269, 3, 5, 13, 3, 3, 7, 3, 727, 11, 3,
    3, 47, 13, 5, 3, 3, 2371, 3, 7, 3, 5, 173,
    3, 11, 3, 3, 3, 5235199, 3, 927472691, 3, 5, 2917, 7,
    5, 3, 3, 3, 5, 43, 3, 167, 3, 5, 3, 13,
    2609, 3, 5, 359, 3, 3, 7, 3, 3, 274525267, 3, 3,
    19, 3, 125527, 7, 3, 5, 3, 3, 3, 3, 3, 3,
    14051, 3, 3, 19, 5, 3, 7, 3, 3, 102161, 3, 40129,
    3, 7, 31, 17609, 5, 7, 3, 23, 3, 5, 11, 3,
    3, 139, 3, 5, 3, 3, 29, 3, 19, 3, 5, 13,
    73, 3, 23, 3, 7, 11, 3, 41, 3, 3, 7, 3,
    5, 3, 3, 3, 47, 5, 3, 170047, 3, 5, 3, 7,
    3, 5, 3, 3, 3, 2741, 7, 3, 5, 79, 3, 3,
    7, 4153, 3, 3, 13, 3, 3, 5, 84809, 3619019, 444060073, 5,
    3, 11, 59, 13, 3, 3, 7, 3, 3, 510089, 3, 5,
    29, 3, 3, 67, 43, 3, 19, 3, 41, 5, 3, 20109319,
    3, 5, 3, 3, 3, 7, 3, 5, 4271, 3, 233, 3,
    3, 7, 3, 243011, 3, 5, 3, 17, 37, 3, 3, 59,
    3, 87223, 3, 11, 5, 3, 3, 107, 17, 3, 7, 5,
    6007, 3, 13, 7, 3, 73, 5, 11, 3, 83, 3, 37,
    3, 5, 3, 463, 3, 3, 3, 3, 5, 2089, 3, 42980801,
    3, 16871, 3, 11, 3, 3, 3, 7, 5, 263, 3, 47626993,
    3, 1753, 3, 19973, 3, 3, 11, 3, 3, 3, 3, 5,
    23, 3, 3, 212419567, 7, 3, 472193, 3, 17, 3, 19, 5,
    3, 171872801, 3, 34629173, 3, 23, 3, 17, 3, 3, 3, 7,
    3, 5, 103, 3, 3, 61, 3, 3, 51817, 3, 5, 3,
    3, 47, 5, 3, 3, 3, 496283, 100297, 3, 37, 3, 3,
    4079, 3, 285569, 3, 3, 3, 11, 29, 3, 7, 3, 17,
    5, 7, 3, 5, 3, 41, 3, 5, 3, 23, 3, 3,
    499, 53, 3, 5, 35543, 3, 3, 7, 3, 7, 17, 3,
    547, 5, 13, 3, 3, 757, 3, 3, 5, 131, 11, 3,
    3, 3, 281, 3, 5, 43, 3, 7, 3, 3, 3, 266660809,
    59, 3, 9323, 3, 7, 3, 5, 200111749, 3, 71, 3, 5,
    11, 3, 3, 6703, 3, 199, 3, 3, 5, 6728047, 43, 7,
    11, 3, 3, 3, 7, 1657, 5, 63625343, 3, 5, 3, 3,
    163, 3, 5, 19, 3, 3, 3, 5, 3, 3, 3, 3,
    29, 3, 5, 149, 3, 3, 3, 5, 199020709, 31, 5, 13,
    3, 3, 5, 11, 3, 3, 7, 3, 5, 13, 3, 3,
    11, 3, 3, 7, 13, 19, 3, 3, 17, 3049, 3, 307,
    5, 3, 3, 1229, 3, 5, 3, 3, 3, 5, 37, 3,
    17, 3, 7, 113, 3, 3, 7, 7414739, 137, 3, 3, 3,
    3, 11, 5, 3, 43, 3, 13, 3, 3, 3, 19, 3,
    6329, 23, 5, 11, 3, 1051, 5, 47, 3, 5, 3, 89681,
    1553, 61, 5, 23, 3, 3, 7, 3, 3, 3, 1012048337, 3,
    3, 211, 11, 3, 5, 7, 3, 29, 89394847, 3, 3, 17,
    3, 3, 3, 5, 3, 47, 3, 3278329, 3, 3, 131, 3,
    13, 3, 7, 3, 3, 5, 3, 7, 117043, 3, 11, 3,
    3, 3, 5, 3, 19, 11, 5, 3, 3, 3, 5, 9931,
    3, 3, 239, 613, 3, 7, 3, 37, 5, 3, 359, 11,
    3, 114157, 59, 3, 103, 19, 3, 3, 7, 5, 3, 3,
    3, 7, 3, 89, 5, 3, 7, 3, 5, 3, 3, 5,
    67, 3, 5, 3, 3, 1248151, 3, 3, 7, 5, 11, 3,
    3, 191, 7, 3, 41, 2531, 5, 1997, 3, 3, 5, 13,
    3, 3, 3, 3, 3233521, 3, 3, 3, 17, 3, 3, 5,
    3, 4430749, 9787, 3, 3, 7, 3, 5, 1867, 3, 3, 167,
    11, 3, 3, 3, 5, 12721, 3, 3, 3, 7643, 3, 6691,
    3, 3, 7, 3, 31, 7, 3, 23, 3, 3847, 3, 5,
    3, 13, 3, 5, 3, 17, 5, 3709, 3, 3, 29, 3,
    192761563, 23, 457943, 3, 17, 3, 3, 7, 43, 5, 3, 3,
    47, 5, 379, 3, 3, 5, 3, 3, 79, 5, 31, 94253,
    11, 3, 109, 3, 3, 67477, 5, 3, 151, 3, 3, 37,
    3, 3, 29, 5, 5, 3, 7, 3, 3, 23, 3, 7,
    3, 3, 3, 3, 3, 5, 13, 11, 3, 3, 31, 1153,
    3, 281, 3, 7, 5, 13, 3, 41, 17293, 3, 7, 3,
    3, 157, 5, 11, 3, 3, 13, 3, 3, 5, 24391, 3,
    5, 3, 3, 347, 3, 5, 3, 3, 7, 3, 3, 59,
    3, 3, 5, 464479, 5, 923015447, 13, 5, 3, 3, 17, 3,
    5, 352973, 661, 11, 3, 3, 7, 61, 3, 3, 3, 43,
    3, 3, 31, 3, 3, 277, 17, 24439, 3, 5, 3, 59,
    11, 5, 7, 3, 3, 1050108233, 3, 3, 3, 158747, 3, 7,
    3, 89, 5, 3, 3, 5, 3, 29, 3, 23, 3, 3,
    3, 3, 5, 53, 3, 13, 3, 3, 5, 163, 3, 3,
    11, 3, 3, 79, 5, 3, 3, 19, 3, 5, 3, 5,
    3, 31, 3, 7, 3, 1540661, 3, 3, 3, 5, 139, 3,
    61, 3, 5, 13, 3, 3, 3, 3, 3, 1711019, 577, 5,
    3, 3, 5, 3, 779990077, 7, 3, 8387, 1303, 3, 23, 7,
    3, 181, 3, 3, 3, 3, 5, 3, 523, 5, 31, 3,
    17, 3, 3, 13, 3, 7, 11, 3, 3, 1993, 3, 3,
    3, 3, 3, 3, 67489, 3, 3, 29, 5, 3, 3, 3,
    5, 137, 19, 37, 7, 3, 47, 3, 7, 3, 5, 461,
    3, 5, 3, 31, 3, 3, 11, 97, 3, 3, 3, 5,
    26557, 3, 337, 3, 11, 3, 157, 3, 349, 5, 13, 7,
    457, 3, 263, 5, 23, 3, 353, 167, 3, 3, 3, 5]

theorem prime_sub_9629 : Nat.Prime (2795935116574469638 - 9629) := by
  show Nat.Prime 2795935116574460009
  exact p2795935116574460009

theorem check_9629 : allC 2795935116574469638 9629 P10k ds_9629 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 2795935116574469638 is 9629. -/
theorem minGB_9629 : minGB 2795935116574469638 = 9629 :=
  minGB_eq_of P10k P10k_complete 2795935116574469638 9629 (by norm_num) (by norm_num) prime_sub_9629 ds_9629 check_9629

def ds_9781 : List ℕ := [
    2, 5, 3, 17, 3, 5, 3, 67, 3, 3, 7517, 437953,
    3, 5, 3, 3, 3, 307, 68007949, 3, 5, 41, 3, 3,
    7, 3, 5, 3, 17, 3, 2121403, 3, 3, 7, 3, 132049,
    11, 5, 3, 3, 3, 7, 3, 5, 3, 470699507, 17, 5,
    3, 23, 3, 3, 12713, 3, 3, 3, 3, 5821, 22201691, 3,
    5, 3, 7, 3, 5, 3, 113, 13, 3, 7, 3, 3,
    23, 5, 103, 3, 3, 89, 3, 4785799, 3, 11, 3, 5,
    49123, 3, 3, 223, 3, 5, 3, 3, 11, 3, 10289, 3,
    3, 3, 5, 797, 55903, 3, 3, 3, 13, 197, 3, 3,
    3, 7, 193, 5, 3, 11, 1960051, 3, 5, 3, 3, 3,
    149, 5, 3, 3, 140521, 3, 7499, 3, 7, 5, 151, 3,
    11, 809, 3, 7, 3, 31, 3, 3, 7, 3, 5, 3,
    168481, 3, 5, 3, 43, 3, 29, 3, 5, 3, 19, 3,
    23, 3, 7, 3, 3, 3, 5569, 3, 3, 3, 1487, 103,
    113, 3, 3, 7, 3, 5, 13, 3, 29, 3, 5, 37,
    79, 3, 5, 3, 3, 3, 13, 5, 17, 3, 5, 3,
    281, 3, 3, 3, 528987703, 5, 3, 3, 3, 7, 244457, 19,
    3, 3, 11, 3, 3, 37, 308119069, 3, 5, 3, 3, 1861,
    3691, 3, 3, 3, 39139, 7, 3, 5, 3, 13, 3, 3,
    3557, 3, 5, 53, 23, 3, 5, 3, 173, 3, 3, 3,
    3, 31, 5, 83, 3, 3, 7, 3, 283, 3, 271, 3,
    3, 7, 3, 3, 911, 67, 3, 73, 5, 3, 643, 5,
    3, 257, 3, 3, 5, 3, 11, 23, 5, 197, 7, 5,
    3, 4844101, 41, 3, 3, 61, 3, 7, 1979, 3, 5, 3,
    499, 3, 3, 3, 3, 3, 5, 3, 641, 3, 3, 7,
    5, 3, 89, 3, 71, 858573953, 3, 7, 3, 5, 3, 3,
    3, 5, 3, 31, 3, 3, 5, 3, 13, 11, 3, 5,
    3, 19, 37, 5, 3, 3, 179, 3, 7, 3, 17, 3,
    11, 3, 7, 13, 5, 3, 3, 107187757, 3, 3, 922285031, 107,
    3, 3, 3739, 709, 3, 5, 19, 3, 3, 3, 3, 3,
    23, 3, 3, 3, 11, 5, 3, 5, 13, 3, 41, 3,
    3, 151, 17, 3, 3, 5, 3, 7, 3, 3, 31, 3,
    7, 3, 68491, 13, 5, 3, 3588503, 3, 3, 659, 3, 5,
    321188237, 3, 11, 3, 1781410259, 3, 449, 3, 3, 29, 11, 3,
    5, 3, 5, 3, 3, 23, 281, 3, 3, 443, 3, 3,
    3, 11159, 3, 3, 5, 3, 3, 3, 73, 3, 239, 3,
    31, 3, 7, 3, 53, 11, 13, 7, 3, 3, 38959, 3,
    7, 3, 5, 3, 17, 43, 19, 3, 3, 3, 653, 3,
    400657, 3, 5, 3, 11, 17, 3, 13, 233, 5, 139, 3,
    3, 7, 5, 3, 3, 697064437, 3, 5, 3, 11, 3, 3,
    5, 3, 7, 3, 5, 3, 103, 3, 7, 37, 1621, 3,
    19, 3, 3, 7, 324619, 3, 127, 169613359, 3, 5, 3, 571,
    5, 3, 3, 59, 67, 5, 3, 3, 5, 3, 13, 43,
    3, 7, 3, 529558781, 5, 48407, 3, 3, 13, 3, 5, 3,
    3, 3, 5, 3, 13, 3, 5, 3, 7, 3, 25237, 102647,
    3, 3, 7, 3, 3, 79, 5, 3, 26768513, 3, 3, 5,
    3, 3, 3, 863, 61, 3, 11, 311, 3, 3, 3, 5,
    19, 109, 3, 7, 3, 3, 5, 3, 13, 37, 8929, 3,
    3, 1009, 3, 23, 3, 5, 3, 3, 41, 3, 5, 3,
    3, 7, 19, 3, 7, 3, 29, 5, 3, 3, 3, 3,
    3, 5, 19, 11, 3, 3, 3, 3, 5, 3, 7, 5,
    3, 371299, 3, 3, 7, 167, 71, 3, 7, 17, 5, 37,
    3, 53, 3, 3, 1093, 417559, 5, 3, 3, 3, 3, 3,
    5, 43, 3, 3, 7, 5, 3, 12197, 3, 3, 7, 5,
    3, 509, 13, 3, 3, 3, 5, 11, 3, 3, 5, 3,
    3, 67607, 53, 3, 7, 3, 43, 5, 41, 3, 3, 7,
    3, 5, 3, 3, 23, 113, 3, 3, 3, 146381, 11, 5,
    251, 3, 3, 1381, 3, 7, 3, 23, 17, 29, 3, 5,
    3, 3, 3, 3, 447382349, 3, 3, 3, 5, 3, 7, 3,
    3, 3, 3, 3, 13, 5, 3, 71, 7, 11, 3, 5,
    105361511, 3, 3, 127219, 3, 3, 5, 3, 3, 409, 317, 3,
    7, 5, 11, 3, 19, 3, 5, 3, 7, 67, 3, 5,
    3, 24469, 3, 5, 1301, 3, 11, 3, 3, 41, 3, 5,
    23, 2311, 3, 40903, 3, 3, 3, 17, 79, 1619, 3, 3,
    7, 61, 3, 3, 239, 3, 62762897, 3, 3, 5, 3, 3,
    5, 3, 3, 383, 3, 3, 19, 5, 3, 3, 157, 5,
    1213, 3, 1459, 3, 3, 269, 3, 5, 3, 19, 5, 3,
    3, 107, 3, 563, 137, 3, 7, 1774369, 3, 3, 3, 7,
    43, 3, 3, 23, 3, 3, 3, 3, 212123, 5, 3, 3,
    11, 31, 5, 19, 3, 7, 13, 11, 3, 67, 3433, 3,
    7, 3, 3, 83, 53, 3, 5, 3, 3, 51496997, 13, 3,
    3, 7, 29, 17, 3, 3, 659, 5, 173, 3, 7, 3,
    5, 101, 3, 5, 3, 3, 5, 3, 37511, 3, 5, 3,
    5, 3, 11197, 3, 17, 3, 3, 3, 4639, 5, 3, 1723,
    3, 3, 3, 19, 3, 186131059, 13, 3, 3, 3, 23, 154131799,
    3, 3, 3, 7, 137, 3, 431, 7, 3, 3, 3, 3,
    3, 23, 3, 2707, 19, 3, 3, 1039, 3, 5, 11, 3,
    7, 5, 3, 3, 3, 31, 3, 43, 7, 3, 5, 3,
    11, 127, 5, 12503, 11, 3, 3, 3, 41, 229, 3, 3,
    7, 3, 37, 3, 3, 3, 23399, 3, 3, 11, 3, 20161,
    5, 3, 3, 3, 13, 5, 3, 67867, 7742593, 3, 3, 13,
    3, 11, 61, 3, 7, 3, 173, 5, 3, 7, 5, 3,
    17, 73, 3, 3, 3, 3, 3, 3, 7, 5, 3, 11,
    3, 3, 3, 3, 3109, 5, 3, 3, 7, 5, 5, 3,
    11, 62003, 3, 5, 13, 3, 3, 3, 19, 3, 271, 3,
    3, 3, 3, 7, 17, 3, 769, 1439, 11, 3, 16651, 3,
    5, 3, 3, 5, 17, 3, 7, 3, 5, 3, 349, 19,
    7, 5, 3, 3, 211, 3, 102552563, 61, 3, 3, 19, 5,
    3, 67, 113, 3, 3, 83, 13, 3, 7, 3, 5, 3,
    7, 3, 31, 3, 5, 3, 547149613, 2857, 23, 3, 3, 17,
    3, 41, 3, 3, 7, 5, 8296159, 1399, 11, 3, 3, 3,
    13, 17, 3, 5, 3, 3, 145726969, 3, 3, 13, 3, 3,
    5, 3, 19, 5, 5, 15739, 3, 59, 3, 3, 3, 31,
    3, 7, 223503701, 3, 5, 3, 3, 5, 209701823, 3, 11, 53,
    5, 10184773, 7, 5, 3, 13, 31, 3, 3, 41, 17, 11,
    3, 3, 3, 3, 3, 587, 3, 163, 3, 5, 3, 3,
    22081777, 3, 7, 3, 5, 269, 3, 3, 17, 11, 5, 3,
    3, 7, 3, 5, 3, 433, 3, 5, 3, 3, 3, 3,
    3, 1450391, 3, 3, 3, 7, 3, 3, 149, 5, 13, 3,
    3, 7, 5, 59, 11, 3, 71, 3, 13, 3, 57319159, 5,
    101, 3, 3, 3, 102149]

theorem prime_sub_9781 : Nat.Prime (3325581707333960528 - 9781) := by
  show Nat.Prime 3325581707333950747
  exact p3325581707333950747

theorem check_9781 : allC 3325581707333960528 9781 P10k ds_9781 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 3325581707333960528 is 9781. -/
theorem minGB_9781 : minGB 3325581707333960528 = 9781 :=
  minGB_eq_of P10k P10k_complete 3325581707333960528 9781 (by norm_num) (by norm_num) prime_sub_9781 ds_9781 check_9781

end LeanLab.Verifications.Top50.Records3
