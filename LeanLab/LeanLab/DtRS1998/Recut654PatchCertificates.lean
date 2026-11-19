/-
AI wrote this Lean code for CODEX task654b.
P0037 page 212 individual primality certification, supporting checked companion patches.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Pock

namespace LeanLab.DtRS1998.Recut654PatchCertificates

/-- A checked numeric witness table transports certified primes to missing bitmap indices. -/
theorem prime_patches_of_chain (lo : ℕ) (ss ks : List ℕ)
    (cs : List Big.Cert) (ps : List (ℕ × ℕ))
    (hc : ∀ c ∈ cs, c.1.Prime)
    (h : ks.all (fun k => ps.any (fun x =>
      (((x.1 == k) && ss.contains x.2) && decide (x.2 ≤ lo + k)) &&
        (cs.map Prod.fst).contains (lo + k - x.2))) = true) :
    ∀ k ∈ ks, ∃ s ∈ ss, s ≤ lo + k ∧ (lo + k - s).Prime := by
  intro k hk
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp (List.all_eq_true.mp h k hk)
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
    decide_eq_true_eq] at hx
  obtain ⟨⟨⟨_, hs⟩, hle⟩, hp⟩ := hx
  obtain ⟨c, hcm, he⟩ := List.mem_map.mp hp
  refine ⟨x.2, hs, hle, ?_⟩
  rw [← he]
  exact hc c hcm

end LeanLab.DtRS1998.Recut654PatchCertificates
