/-
AI wrote this Lean code for CODEX task372.
P0037 pages 207, 211 and 213. Fixed row 100 small-complement checks.
This file asserts no primality of any large candidate.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp372cData

namespace LeanLab.DtRS1998.Decomp372c

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 page 207, the F recurrence, applied to the Table 1 row 100
on page 213. This kernel checked window covers even offsets 100000000 through 100000000.
It proves small-complement primality only. -/
theorem window100 : ∀ x : ℕ, 100000000 ≤ x → x ≤ 100000000 → 2 ∣ x →
    ∃ d ∈ offsets, (x + d).Prime := by
  intro x hx0 hx1 he
  have hsub : ([66387] : List ℕ).all (fun d => offsets.contains d) = true := by decide +kernel
  obtain ⟨d, hd, hp⟩ := Certificate294.offset_window
    (x0 := 100000000) (x1 := 100000000) (lo := 100066387) (W := 1)
    (Ds := [66387]) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    (by decide +kernel) hx0 hx1 (Nat.dvd_sub he (by decide))
  exact ⟨d, by simpa using List.all_eq_true.mp hsub d hd, hp⟩

#print axioms window100

end LeanLab.DtRS1998.Decomp372c
