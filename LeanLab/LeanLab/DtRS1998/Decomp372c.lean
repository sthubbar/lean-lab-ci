/-
AI wrote this Lean code for CODEX task372.
P0037 Section 5.1 page 211 and Table 1 page 213, row 10^100.
The explicit candidate list separates primality from small-prime coverage.
Its reconstruction uses probable primality only and supplies no primality proof.
The final certificate is CONDITIONAL ON the open large candidate primality leaf.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp372cData
import LeanLab.DtRS1998.Decomp372cWindows20
import LeanLab.DtRS1998.Decomp372cWindows19
import LeanLab.DtRS1998.Decomp372cWindows18
import LeanLab.DtRS1998.Decomp372cWindows17
import LeanLab.DtRS1998.Decomp372cWindows16
import LeanLab.DtRS1998.Decomp372cWindows15
import LeanLab.DtRS1998.Decomp372cWindows14
import LeanLab.DtRS1998.Decomp372cWindows13
import LeanLab.DtRS1998.Decomp372cWindows12
import LeanLab.DtRS1998.Decomp372cWindows11
import LeanLab.DtRS1998.Decomp372cWindows10
import LeanLab.DtRS1998.Decomp372cWindows9
import LeanLab.DtRS1998.Decomp372cWindows8
import LeanLab.DtRS1998.Decomp372cWindows7
import LeanLab.DtRS1998.Decomp372cWindows6
import LeanLab.DtRS1998.Decomp372cWindows5
import LeanLab.DtRS1998.Decomp372cWindows4
import LeanLab.DtRS1998.Decomp372cWindows3
import LeanLab.DtRS1998.Decomp372cWindows2
import LeanLab.DtRS1998.Decomp372cWindows1
import LeanLab.DtRS1998.Decomp372cWindows0
import LeanLab.DtRS1998.PocklingtonB7Row100

namespace LeanLab.DtRS1998.Decomp372c

open Certificate294

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- LEAF. P0037 Section 5.1 page 211, primality certification paragraph,
and Table 1 page 213, row 10^100. Prove primality of this fixed list only.
This leaf asserts no Goldbach coverage. Full prime certificates are OPEN.
ROUTE BURST 7: proved from `PocklingtonB7Row100.qs_prime`, the kernel checked Pocklington
certificates, and so CONDITIONAL only on that file's `hard_prime` leaf while it is open. -/
theorem candidate_primes : ∀ q ∈ qs, q.Prime := by
  exact PocklingtonB7Row100.qs_prime

/-- LEAF. P0037 page 207, the displayed recurrence for F,
Section 5.1 page 211 and Table 1 page 213, row 10^100.
Every even offset through 10^8 has a prime small complement in the fixed list.
This leaf asserts no primality of the large candidates. The finite check is assembled from the accepted windows below. -/
theorem offset_cover :
    ∀ x : ℕ, x ≤ 10 ^ 8 → 2 ∣ x → ∃ d ∈ offsets, (x + d).Prime := by
  intro x hx he
  generalize hk : x / 1000000 = k
  have hkle : k ≤ 100 := by omega
  interval_cases k
  · exact window0 x (by omega) (by omega) he
  · exact window1 x (by omega) (by omega) he
  · exact window2 x (by omega) (by omega) he
  · exact window3 x (by omega) (by omega) he
  · exact window4 x (by omega) (by omega) he
  · exact window5 x (by omega) (by omega) he
  · exact window6 x (by omega) (by omega) he
  · exact window7 x (by omega) (by omega) he
  · exact window8 x (by omega) (by omega) he
  · exact window9 x (by omega) (by omega) he
  · exact window10 x (by omega) (by omega) he
  · exact window11 x (by omega) (by omega) he
  · exact window12 x (by omega) (by omega) he
  · exact window13 x (by omega) (by omega) he
  · exact window14 x (by omega) (by omega) he
  · exact window15 x (by omega) (by omega) he
  · exact window16 x (by omega) (by omega) he
  · exact window17 x (by omega) (by omega) he
  · exact window18 x (by omega) (by omega) he
  · exact window19 x (by omega) (by omega) he
  · exact window20 x (by omega) (by omega) he
  · exact window21 x (by omega) (by omega) he
  · exact window22 x (by omega) (by omega) he
  · exact window23 x (by omega) (by omega) he
  · exact window24 x (by omega) (by omega) he
  · exact window25 x (by omega) (by omega) he
  · exact window26 x (by omega) (by omega) he
  · exact window27 x (by omega) (by omega) he
  · exact window28 x (by omega) (by omega) he
  · exact window29 x (by omega) (by omega) he
  · exact window30 x (by omega) (by omega) he
  · exact window31 x (by omega) (by omega) he
  · exact window32 x (by omega) (by omega) he
  · exact window33 x (by omega) (by omega) he
  · exact window34 x (by omega) (by omega) he
  · exact window35 x (by omega) (by omega) he
  · exact window36 x (by omega) (by omega) he
  · exact window37 x (by omega) (by omega) he
  · exact window38 x (by omega) (by omega) he
  · exact window39 x (by omega) (by omega) he
  · exact window40 x (by omega) (by omega) he
  · exact window41 x (by omega) (by omega) he
  · exact window42 x (by omega) (by omega) he
  · exact window43 x (by omega) (by omega) he
  · exact window44 x (by omega) (by omega) he
  · exact window45 x (by omega) (by omega) he
  · exact window46 x (by omega) (by omega) he
  · exact window47 x (by omega) (by omega) he
  · exact window48 x (by omega) (by omega) he
  · exact window49 x (by omega) (by omega) he
  · exact window50 x (by omega) (by omega) he
  · exact window51 x (by omega) (by omega) he
  · exact window52 x (by omega) (by omega) he
  · exact window53 x (by omega) (by omega) he
  · exact window54 x (by omega) (by omega) he
  · exact window55 x (by omega) (by omega) he
  · exact window56 x (by omega) (by omega) he
  · exact window57 x (by omega) (by omega) he
  · exact window58 x (by omega) (by omega) he
  · exact window59 x (by omega) (by omega) he
  · exact window60 x (by omega) (by omega) he
  · exact window61 x (by omega) (by omega) he
  · exact window62 x (by omega) (by omega) he
  · exact window63 x (by omega) (by omega) he
  · exact window64 x (by omega) (by omega) he
  · exact window65 x (by omega) (by omega) he
  · exact window66 x (by omega) (by omega) he
  · exact window67 x (by omega) (by omega) he
  · exact window68 x (by omega) (by omega) he
  · exact window69 x (by omega) (by omega) he
  · exact window70 x (by omega) (by omega) he
  · exact window71 x (by omega) (by omega) he
  · exact window72 x (by omega) (by omega) he
  · exact window73 x (by omega) (by omega) he
  · exact window74 x (by omega) (by omega) he
  · exact window75 x (by omega) (by omega) he
  · exact window76 x (by omega) (by omega) he
  · exact window77 x (by omega) (by omega) he
  · exact window78 x (by omega) (by omega) he
  · exact window79 x (by omega) (by omega) he
  · exact window80 x (by omega) (by omega) he
  · exact window81 x (by omega) (by omega) he
  · exact window82 x (by omega) (by omega) he
  · exact window83 x (by omega) (by omega) he
  · exact window84 x (by omega) (by omega) he
  · exact window85 x (by omega) (by omega) he
  · exact window86 x (by omega) (by omega) he
  · exact window87 x (by omega) (by omega) he
  · exact window88 x (by omega) (by omega) he
  · exact window89 x (by omega) (by omega) he
  · exact window90 x (by omega) (by omega) he
  · exact window91 x (by omega) (by omega) he
  · exact window92 x (by omega) (by omega) he
  · exact window93 x (by omega) (by omega) he
  · exact window94 x (by omega) (by omega) he
  · exact window95 x (by omega) (by omega) he
  · exact window96 x (by omega) (by omega) he
  · exact window97 x (by omega) (by omega) he
  · exact window98 x (by omega) (by omega) he
  · exact window99 x (by omega) (by omega) he
  · exact window100 x (by omega) (by omega) he

/-- CONDITIONAL ON candidate_primes. offset_cover is proved.
P0037 Section 5.1 page 211 and Table 1 page 213.
This is the exact statement of Decomp270a.certificate100. -/
theorem certificate100 :
    ∃ qs : List ℕ, qs.length ≤ 250 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 100 - 68969 ≤ q ∧ q ≤ 10 ^ 100) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 100 + 2 * j ∧ (10 ^ 100 + 2 * j - q).Prime))) = true := by
  refine ⟨qs, by rw [length_eq], ?_, ?_⟩
  · intro q hq
    exact ⟨candidate_primes q hq, bounds q hq⟩
  · exact offsets_certificate
      (fun d hd => le_trans (offset_bounds d hd) (by norm_num)) offset_cover

#print axioms offset_zero_instance
#print axioms length_eq
#print axioms offset_bounds
#print axioms bounds
#print axioms candidate_primes
#print axioms offset_cover
#print axioms certificate100

end LeanLab.DtRS1998.Decomp372c
