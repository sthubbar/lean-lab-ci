/-
P0006 page 3, Section 4, checking stored Proth certificates.
This specifies the mathematical checks on stored coefficients and witnesses.
The paper's full range data remain cited. AI wrote the Lean code.
Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.HelfgottPlattU1401Bundle

namespace LeanLab.HelfgottPlatt.Task133

/-- Page 3, the values represented by stored coefficient and witness pairs
at a fixed Proth exponent m plus one. -/
def certificateValues (m : ℕ) (rows : List (ℕ × ℕ)) : List ℕ :=
  rows.map (fun ka => ka.1 * 2 ^ (m + 1) + 1)

/-- Page 3, primality part of the stored certificate check. Passing all
Proth tests proves every represented rung prime. -/
theorem certificateValues_prime {m : ℕ} {rows : List (ℕ × ℕ)}
    (h : rows.all (fun ka => Proth.prothB ka.1 m ka.2) = true) :
    ∀ p ∈ certificateValues m rows, p.Prime := by
  intro p hp
  obtain ⟨ka, hka, rfl⟩ := List.mem_map.mp hp
  exact Proth.prime_of_prothB (List.all_eq_true.mp h ka hka)

/-- Page 3, executable mathematical range checks on stored Proth pairs.
Check primality, increasing sharp gaps and both endpoint overlap conditions. -/
def certificateRangeCheck (m H W i : ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | ka :: rows =>
    let h := ka.1 * 2 ^ (m + 1) + 1
    let t := certificateValues m rows
    (ka :: rows).all (fun kb => Proth.prothB kb.1 m kb.2) &&
      decide (3 ≤ h) && U6816.Top.chainB2 (2 * H) (h :: t) &&
        decide (h ≤ i * W + H) && decide ((i + 1) * W < t.getLastD h + H)

/-- Page 3, passing stored Proth certificate checks produces the existing
range condition consumed by the paper's ladder reduction. -/
theorem certificateRangeCheck_sound {m H W i : ℕ} {rows : List (ℕ × ℕ)}
    (h : certificateRangeCheck m H W i rows = true) :
    U1401.RangeOKG H W i (certificateValues m rows) := by
  cases rows with
  | nil => simp [certificateRangeCheck] at h
  | cons ka rows =>
    simp only [certificateRangeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hall, h3⟩, hchain⟩, hstart⟩, hend⟩ := h
    have hp := certificateValues_prime hall
    refine ⟨ka.1 * 2 ^ (m + 1) + 1, certificateValues m rows, rfl,
      hp _ (by simp [certificateValues]), h3, ?_,
        U6816.Top.chainB2_sound (2 * H) _ hchain, hstart, hend⟩
    intro p hmem
    apply hp p
    exact List.mem_cons_of_mem _ hmem

/-- Page 3, a concrete nonempty passing range certificate. With exponent
two, the stored pairs certify five and thirteen and meet all overlap checks
for half bound ten, width twenty and range index zero. -/
theorem certificate_range_instance :
    certificateRangeCheck 1 10 20 0 [(1, 2), (3, 2)] = true ∧
      U1401.RangeOKG 10 20 0 (certificateValues 1 [(1, 2), (3, 2)]) := by
  have h : certificateRangeCheck 1 10 20 0 [(1, 2), (3, 2)] = true := by decide +kernel
  exact ⟨h, certificateRangeCheck_sound h⟩

end LeanLab.HelfgottPlatt.Task133
