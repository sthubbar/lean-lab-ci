/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting certificate representation.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task71Paper
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.Task303

open LeanLab Task71.Paper

/-- A finite interval proof supplies a finite prime list in the exact leaf format.
P0037 Section 4.1 pages 209 and 210, supporting finite list representation.
CONDITIONAL ON the supplied interval proof. -/
theorem certificate_of_interval {B L : ℕ} (hB : Even B) (h : IntervalSum B L) :
    ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
      (List.range (L / 2 + 1)).all (fun j =>
        qs.any (fun q => decide (q ≤ B + 2*j ∧ (B + 2*j - q).Prime))) = true := by
  let qs := (List.range (B + L + 1)).filter (fun q => decide q.Prime)
  refine ⟨qs, ?_, ?_⟩
  · intro q hq
    exact of_decide_eq_true (List.mem_filter.mp hq).2
  · apply List.all_eq_true.mpr
    intro j hj
    have hjL := List.mem_range.mp hj
    have hj2 : 2*j ≤ L := by omega
    have he : Even (B + 2*j) := even_iff_two_dvd.mpr
      (dvd_add (even_iff_two_dvd.mp hB) (dvd_mul_right 2 j))
    obtain ⟨p, q, hp, hq, hs⟩ := h (B + 2*j) (by omega) (by omega) he
    apply List.any_eq_true.mpr
    refine ⟨p, ?_, decide_eq_true ⟨by omega, ?_⟩⟩
    · exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), decide_eq_true hp⟩
    · convert hq using 1 <;> omega

/-- The hypotheses of the representation theorem hold on a nonempty interval.
P0037 Section 4.1 pages 209 and 210, supporting concrete instance. -/
theorem finite_list_instance :
    ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
      (List.range (4 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide (q ≤ 6 + 2*j ∧ (6 + 2*j - q).Prime))) = true := by
  apply certificate_of_interval (by decide)
  intro n hlo hhi he
  obtain ⟨j, hj⟩ := he
  have hjlo : 3 ≤ j := by omega
  have hjhi : j ≤ 5 := by omega
  interval_cases j
  · exact ⟨3, 3, by decide, by decide, by omega⟩
  · exact ⟨3, 5, by decide, by decide, by omega⟩
  · exact ⟨3, 7, by decide, by decide, by omega⟩

#print axioms certificate_of_interval
#print axioms finite_list_instance

end LeanLab.DtRS1998.Task303
