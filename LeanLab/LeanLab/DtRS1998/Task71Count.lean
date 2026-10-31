/-
AI wrote this Lean code for CODEX task71.
P0037, printed page 213, Table 1.
Exact prime enumeration from Pocklington primes and composite witnesses.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.DtRS1998U6828Chk

namespace LeanLab.DtRS1998.Task71

open U6828

/-- A prime marker or a certificate excluding the current odd integer. -/
def entry (ps : List ℕ) (x : ℕ) (c : ℕ × ℕ) : Bool :=
  if c.1 = 1 then ps.contains x else entN x c

theorem entry_sound {ps : List ℕ} {x : ℕ} {c : ℕ × ℕ}
    (h : entry ps x c = true) (hx : x.Prime) : x ∈ ps := by
  unfold entry at h
  split at h
  · exact List.contains_iff_mem.mp h
  · exact False.elim (entN_sound h hx)

/-- Every odd integer consumes one marker or composite witness. -/
def cover (ps : List ℕ) : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | _, 0, _ => true
  | m, k + 1, cs =>
    if m % 2 = 0 then cover ps (m + 1) k cs else
    match cs with
    | [] => false
    | c :: rest => entry ps m c && cover ps (m + 1) k rest

theorem cover_sound (ps : List ℕ) : ∀ k m cs, 3 ≤ m → cover ps m k cs = true →
    ∀ x, m ≤ x → x < m + k → x.Prime → x ∈ ps := by
  intro k
  induction k with
  | zero => intro m cs hm h x h1 h2; omega
  | succ k ih =>
    intro m cs hm h x h1 h2 hx
    unfold cover at h
    by_cases hev : m % 2 = 0
    · rw [if_pos hev] at h
      by_cases hxm : x = m
      · subst x
        have := hx.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hev)
        omega
      · exact ih (m + 1) cs (by omega) h x (by omega) (by omega) hx
    · rw [if_neg hev] at h
      match cs, h with
      | c :: rest, h =>
        simp only [Bool.and_eq_true] at h
        by_cases hxm : x = m
        · subst x
          exact entry_sound h.1 hx
        · exact ih (m + 1) rest (by omega) h.2 x (by omega) (by omega) hx

/-- Primes in a closed interval, including its endpoints. -/
def primesIn (a b : ℕ) : Finset ℕ := (Finset.Icc a b).filter Nat.Prime

theorem primesIn_eq {ps : List ℕ} {a b : ℕ}
    (hp : ∀ p ∈ ps, p.Prime)
    (hr : ∀ p ∈ ps, a ≤ p ∧ p ≤ b)
    (hc : ∀ p, a ≤ p → p ≤ b → p.Prime → p ∈ ps) :
    primesIn a b = ps.toFinset := by
  ext p
  simp only [primesIn, Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset]
  exact ⟨fun h => hc p h.1.1 h.1.2 h.2, fun h => ⟨hr p h, hp p h⟩⟩

/-- Restrict a certified complete list at an inclusive upper bound. -/
theorem primesIn_prefix {ps : List ℕ} {a b t : ℕ}
    (hp : ∀ p ∈ ps, p.Prime)
    (hr : ∀ p ∈ ps, a ≤ p ∧ p ≤ b)
    (hc : ∀ p, a ≤ p → p ≤ b → p.Prime → p ∈ ps) (ht : t ≤ b) :
    primesIn a t = (ps.filter (fun p => p ≤ t)).toFinset := by
  apply primesIn_eq
  · intro p h
    exact hp p (List.mem_filter.mp h).1
  · intro p h
    obtain ⟨hm, hb⟩ := List.mem_filter.mp h
    exact ⟨(hr p hm).1, of_decide_eq_true hb⟩
  · intro p hpa hpt hprime
    exact List.mem_filter.mpr ⟨hc p hpa (hpt.trans ht) hprime, decide_eq_true hpt⟩

/-- One based local prime index. -/
def HasPrimeIndex (a p n : ℕ) : Prop := p.Prime ∧ a ≤ p ∧ (primesIn a p).card = n

/-- Concrete nonvacuity checks for the scanner and local index. -/
theorem cover_instance : cover [3, 5] 3 4 [(1, 0), (1, 0)] = true := by decide +kernel

theorem index_instance : HasPrimeIndex 3 5 2 := by
  unfold HasPrimeIndex primesIn
  decide +kernel

end LeanLab.DtRS1998.Task71
