/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Data

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async true

/-- Even offsets in closed window 100 have a prime complement, page 210. -/
theorem window100 : ∀ x : ℕ, 100000000 ≤ x → x ≤ 100000000 → 2 ∣ x →
    ∃ d ∈ offsets, (x + d).Prime := by
  intro x hx0 hx1 he
  have hsub : ([213] : List ℕ).all (fun d => offsets.contains d) = true := by decide +kernel
  obtain ⟨d, hd, hp⟩ := offset_window (x0 := 100000000) (x1 := 100000000) (lo := 100000213) (W := 1)
    (Ds := [213]) (by decide) (by norm_num [B2]) (by decide +kernel)
    (by decide +kernel) hx0 hx1 (Nat.dvd_sub he (by decide))
  exact ⟨d, by simpa using List.all_eq_true.mp hsub d hd, hp⟩

#print axioms window100

end LeanLab.DtRS1998.Task303.Middle1
