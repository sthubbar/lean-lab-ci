/-
P0073, Section 2, page 428. Arbitrary unbounded odd input.
AI wrote this Lean code for CODEX task114. Goldbach is open.
-/
import LeanLab.SteinStein1965.Distinct
namespace LeanLab.Stein1965.General114

open LeanLab.SteinStein1965
/-- Page 428: an unbounded odd input admits a fresh valid S-step beyond any bound. -/
theorem unbounded_input_step (isA : ℕ → Bool) (B : List ℕ) (L : ℕ)
    (hodd : ∀ a, isA a = true → Odd a)
    (hunbounded : ∀ M, ∃ a, M ≤ a ∧ isA a = true)
    (hseed : ∃ b ∈ B, Odd b) :
    ∃ e a, L ≤ e ∧ Even e ∧ step isA (B, []) e = (B ++ [a], []) ∧
      isA a = true ∧ Odd a ∧ a ∉ B := by
  obtain ⟨b, hb, hbodd⟩ := hseed
  obtain ⟨a, habound, haA⟩ := hunbounded (L + 2 * B.sum + 1)
  let e := a + b
  have hc : covers B e = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    obtain ⟨x, hx, y, hy, hxy⟩ := (covers_iff B e).mp htrue
    have hx' := List.le_sum_of_mem hx
    have hy' := List.le_sum_of_mem hy
    dsimp [e] at hxy
    omega
  have hsub : e - b = a := by dsimp [e]; omega
  have hmem : a ∈ cands isA B e := by
    simp only [cands, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨b, ⟨hb, by dsimp [e]; omega, by simpa [hsub] using haA⟩, hsub⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (List.isSome_max?_of_mem hmem)
  have hqmem := List.max?_mem hq
  have hqA := (mem_cands hqmem).1
  refine ⟨e, q, by dsimp [e]; omega, (hodd a haA).add_odd hbodd, ?_,
    hqA, hodd q hqA, fresh_candidate isA B e q hc hqmem⟩
  simp [step, hc, hq]

/-- Page 428: an infinite odd input has a valid fresh future S-step. -/
theorem infinite_input_step (isA : ℕ → Bool) (B : List ℕ) (L : ℕ)
    (hodd : ∀ a, isA a = true → Odd a)
    (hinfinite : {a | isA a = true}.Infinite)
    (hseed : ∃ b ∈ B, Odd b) :
    ∃ e a, L ≤ e ∧ Even e ∧ step isA (B, []) e = (B ++ [a], []) ∧
      isA a = true ∧ Odd a ∧ a ∉ B := by
  apply unbounded_input_step isA B L hodd _ hseed
  intro M
  obtain ⟨a, ha, hMa⟩ := hinfinite.exists_gt M
  exact ⟨a, hMa.le, ha⟩

end LeanLab.Stein1965.General114
