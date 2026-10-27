/-
P0073, Section 2, equations 2.2 and 2.3, pages 427 and 428.
Correctness of the bounded search in the original Stein1965 folder.
AI wrote this Lean code for CODEX task114. Goldbach is open.
-/
import LeanLab.Stein1965.Statements
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.Stein1965

/-- Equation 2.2, page 427: Boolean coverage is exactly membership in the sumset. -/
theorem covered_iff (B : List ℕ) (e : ℕ) :
    covered B e = true ↔ ∃ b ∈ B, ∃ c ∈ B, b + c = e := by
  simp [covered, List.any_eq_true]

/-- Equation 2.3, page 427: the original accumulator is the standard list maximum. -/
theorem bestA_eq_max? (p0 : ℕ) (B : List ℕ) (e : ℕ) :
    bestA p0 B e =
      (B.filterMap fun b => if b < e && p0 ≤ e - b && primeB (e - b)
        then some (e - b) else none).max? := by
  unfold bestA
  generalize (B.filterMap fun b => if b < e && p0 ≤ e - b && primeB (e - b)
    then some (e - b) else none) = L
  cases L with
  | nil => rfl
  | cons a L =>
    rw [List.foldl_cons]
    exact List.foldl_hom some (fun x y => rfl)

/-- Equation 2.3, page 427: candidates are exactly admissible prime complements. -/
theorem mem_candidates_iff (p0 : ℕ) (B : List ℕ) (e a : ℕ) :
    a ∈ (B.filterMap fun b => if b < e && p0 ≤ e - b && primeB (e - b)
      then some (e - b) else none) ↔
    a.Prime ∧ p0 ≤ a ∧ ∃ b ∈ B, a + b = e := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, ha⟩
    split_ifs at ha with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have heq : e - b = a := Option.some.inj ha
      exact ⟨primeB_sound (heq ▸ hc.2), heq ▸ hc.1.2,
        b, hb, by omega⟩
  · rintro ⟨ha, hp0, b, hb, hab⟩
    refine ⟨b, hb, ?_⟩
    have hae : e - b = a := by omega
    have hlt : b < e := by have := ha.two_le; omega
    simp [hlt, hae, hp0, LeanLab.SteinStein1965.primeB_complete ha]

/-- Equation 2.3, page 427: bestA returns precisely the largest admissible prime. -/
theorem bestA_spec (p0 : ℕ) (B : List ℕ) (e a : ℕ) :
    bestA p0 B e = some a ↔
    (a.Prime ∧ p0 ≤ a ∧ ∃ b ∈ B, a + b = e) ∧
      ∀ q, q.Prime → p0 ≤ q → (∃ b ∈ B, q + b = e) → q ≤ a := by
  rw [bestA_eq_max?, List.max?_eq_some_iff]
  simp only [mem_candidates_iff]
  aesop

/-- Page 428: a successful search hits an uncovered target within its fuel window. -/
theorem findNew_hit (p0 : ℕ) (B : List ℕ) (fuel e a : ℕ)
    (h : findNew p0 B fuel e = some a) :
    ∃ k < fuel, covered B (e + 2 * k) = false ∧
      bestA p0 B (e + 2 * k) = some a := by
  induction fuel generalizing e with
  | zero => simp [findNew] at h
  | succ fuel ih =>
    simp only [findNew] at h
    split at h
    · obtain ⟨k, hk, hc, ha⟩ := ih (e + 2) h
      refine ⟨k + 1, by omega, ?_⟩
      simpa only [show e + 2 * (k + 1) = (e + 2) + 2 * k by omega] using ⟨hc, ha⟩
    · rename_i hc
      split at h
      · rename_i b hb
        have hba : b = a := Option.some.inj h
        subst b
        exact ⟨0, by omega, by simpa using Bool.eq_false_iff.mpr hc,
          by simpa using hb⟩
      · obtain ⟨k, hk, hc, ha⟩ := ih (e + 2) h
        refine ⟨k + 1, by omega, ?_⟩
        simpa only [show e + 2 * (k + 1) = (e + 2) + 2 * k by omega] using ⟨hc, ha⟩

/-- Equations 2.2 and 2.3: a search result is a fresh admissible prime. -/
theorem findNew_sound (p0 : ℕ) (B : List ℕ) (fuel e a : ℕ)
    (h : findNew p0 B fuel e = some a) :
    a.Prime ∧ p0 ≤ a ∧ a ∉ B := by
  obtain ⟨k, _, hc, ha⟩ := findNew_hit p0 B fuel e a h
  obtain ⟨⟨hp, hlo, b, hb, hab⟩, _⟩ := (bestA_spec p0 B (e + 2 * k) a).mp ha
  refine ⟨hp, hlo, ?_⟩
  intro haB
  have ht := (covered_iff B (e + 2 * k)).mpr ⟨a, haB, b, hb, hab⟩
  rw [hc] at ht
  contradiction

/-- Page 428: a reachable uncovered candidate guarantees bounded-search success. -/
theorem findNew_complete (p0 : ℕ) (B : List ℕ) (fuel e k a : ℕ)
    (hk : k < fuel) (hc : covered B (e + 2 * k) = false)
    (ha : bestA p0 B (e + 2 * k) = some a) :
    ∃ q, findNew p0 B fuel e = some q := by
  induction fuel generalizing e k with
  | zero => omega
  | succ fuel ih =>
    cases k with
    | zero =>
      refine ⟨a, ?_⟩
      simp only [Nat.mul_zero, Nat.add_zero] at hc ha
      simp [findNew, hc, ha]
    | succ k =>
      have heq : (e + 2) + 2 * k = e + 2 * (k + 1) := by omega
      obtain ⟨q, hq⟩ := ih (e + 2) k (by omega) (heq ▸ hc) (heq ▸ ha)
      simp only [findNew]
      split
      · exact ⟨q, hq⟩
      · split
        · exact ⟨_, rfl⟩
        · exact ⟨q, hq⟩

/-- Equation 2.2: a target above twice the list sum is uncovered. -/
theorem covered_false_of_large (B : List ℕ) (e : ℕ) (he : 2 * B.sum < e) :
    covered B e = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨b, hb, c, hc, hbc⟩ := (covered_iff B e).mp h
  have hb' := List.le_sum_of_mem hb
  have hc' := List.le_sum_of_mem hc
  omega

/-- Page 428: additional fuel preserves a successful search result. -/
theorem findNew_add_fuel (p0 : ℕ) (B : List ℕ) (fuel e a : ℕ)
    (h : findNew p0 B fuel e = some a) (extra : ℕ) :
    findNew p0 B (fuel + extra) e = some a := by
  induction fuel generalizing e with
  | zero => simp [findNew] at h
  | succ fuel ih =>
    simp only [findNew] at h
    simp only [Nat.succ_add, findNew]
    split at h
    · rename_i hc
      rw [if_pos hc]
      exact ih (e + 2) h
    · rename_i hc
      rw [if_neg hc]
      split at h
      · exact h
      · exact ih (e + 2) h

/-- Page 428: any two successful fuel bounds give the same next element. -/
theorem findNew_unique (p0 : ℕ) (B : List ℕ) (fuel1 fuel2 e a b : ℕ)
    (ha : findNew p0 B fuel1 e = some a)
    (hb : findNew p0 B fuel2 e = some b) : a = b := by
  have ha' := findNew_add_fuel p0 B fuel1 e a ha fuel2
  have hb' := findNew_add_fuel p0 B fuel2 e b hb fuel1
  rw [Nat.add_comm fuel2 fuel1] at hb'
  exact Option.some.inj (ha'.symm.trans hb')

end LeanLab.Stein1965
