/-
AI wrote this Lean code for CODEX task302.
P0037 Section 5.2 page 212 and Table 2 page 214.
The same prime list must serve every block to preserve the sealed size bound.
The implication is CONDITIONAL ON the supplied block checks.
Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.DtRS1998.Task302.Coverage

/-- Fixed-list block checks imply the complete finite certificate.
P0037 Section 5.2 page 212. The last block is clipped at the right endpoint.
CONDITIONAL ON all supplied block checks and prime proofs. -/
theorem certificate_of_blocks {B L K N : ℕ} (qs : List ℕ) (hK : 0 < K)
    (hlen : qs.length ≤ N) (hp : ∀ q ∈ qs, q.Prime)
    (hblocks : ∀ k : ℕ, k ≤ (L / 2) / K →
      (List.range (min K (L / 2 + 1 - K * k))).all (fun t =>
        qs.any (fun q => decide
          (q ≤ B + 2 * (K * k + t) ∧
            (B + 2 * (K * k + t) - q).Prime))) = true) :
    ∃ ps : List ℕ, ps.length ≤ N ∧
      (∀ p ∈ ps, p.Prime) ∧
      (List.range (L / 2 + 1)).all (fun j =>
        ps.any (fun p => decide
          (p ≤ B + 2 * j ∧ (B + 2 * j - p).Prime))) = true := by
  refine ⟨qs, hlen, hp, List.all_eq_true.mpr ?_⟩
  intro j hj
  have hjL : j ≤ L / 2 := by simpa only [List.mem_range, Nat.lt_succ_iff] using hj
  have hk : j / K ≤ (L / 2) / K := Nat.div_le_div_right hjL
  have hmod : j % K < K := Nat.mod_lt _ hK
  have hsplit : j % K + K * (j / K) = j := Nat.mod_add_div _ _
  have ht : j % K ∈ List.range (min K (L / 2 + 1 - K * (j / K))) := by
    rw [List.mem_range, lt_min_iff]
    exact ⟨hmod, by omega⟩
  have h := List.all_eq_true.mp (hblocks (j / K) hk) (j % K) ht
  simpa only [Nat.add_comm (K * (j / K)), hsplit] using h

#print axioms certificate_of_blocks

/-- A nonempty clipped final block covers 6, 8, 10, 12 and 14 using primes 3 and 7.
P0037 Section 5.2 page 212, a small instance of the block format. -/
theorem blocks_instance :
    ∃ qs : List ℕ, qs.length ≤ 2 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 6 + 2 * j ∧ (6 + 2 * j - q).Prime))) = true := by
  apply certificate_of_blocks (B := 6) (L := 8) (K := 3) [3, 7]
    (by decide) (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> decide
  · intro k hk
    have hk' : k ≤ 1 := by simpa using hk
    interval_cases k <;> decide +kernel

#print axioms blocks_instance

end LeanLab.DtRS1998.Task302.Coverage
