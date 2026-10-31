/-
R-5334, CLOUD MANUAL-M3, unit U-7005, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The search route.  Binary Goldbach is the totality of the search problem N ↦ p with
p and N - p prime.  A proved deterministic search is a proof; the least prime search
runs in polylog time iff the least Goldbach prime p(N) is at most log^C N.  The
Tao-Croot-Helfgott method finds primes through the parity of a prime count; for
Goldbach the free parity bit is empty.
* `pb`, `pb_iff`: trial division primality, equal to `Nat.Prime`.
* `lw N`: the least p ≤ N/2 with p and N - p prime, by `List.find?` with `pb`.
* `lw_spec`: what `lw` returns is a witness and every smaller p fails.
* `goldbach_iff_lw`: Goldbach at N iff `lw N` is some p.
* `ordered_parity`: for even N, the ordered count #{0 < p < N : p, N - p prime} is
  odd iff N/2 is prime: the reflection p ↦ N - p pairs the representations and fixes
  only N/2.  So the parity of the Goldbach count carries no information beyond N/2.
* `lw_table_1000`: kernel check, p(N) ≤ 73 for every even N in [4, 1000], and
  `lw_992`: p(992) = 73, the record.  Beyond, Verifications/Pratt.lean proves
  minGB 3325581707333960528 = 9781, the record of Oliveira e Silva, Herzog and Pardi.
-/
import Mathlib

namespace LeanLab.Routes.R5334

open Finset

/-- Trial division primality, cheap in the kernel. -/
def pb (n : ℕ) : Bool := decide (2 ≤ n) && (List.range' 2 (n - 2)).all (fun d => n % d != 0)

theorem pb_iff (n : ℕ) : pb n = true ↔ n.Prime := by
  unfold pb
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, Nat.prime_def_lt']
  simp only [List.mem_range'_1, bne_iff_ne, ne_eq, ← Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨h2, h⟩; exact ⟨h2, fun m hm hmn => h m ⟨hm, by omega⟩⟩
  · rintro ⟨h2, h⟩; exact ⟨h2, fun m hm => h m hm.1 (by omega)⟩

/-- The least p ≤ N/2 with p and N - p prime. -/
def lw (N : ℕ) : Option ℕ :=
  (List.range (N / 2 + 1)).find? (fun p => pb p && pb (N - p))

theorem lw_spec {N p : ℕ} (h : lw N = some p) :
    p.Prime ∧ (N - p).Prime ∧ 2 * p ≤ N ∧ ∀ q < p, ¬ (q.Prime ∧ (N - q).Prime) := by
  unfold lw at h
  rw [List.find?_eq_some_iff_getElem] at h
  obtain ⟨hp, i, hi, hpi, hbefore⟩ := h
  simp only [Bool.and_eq_true, pb_iff] at hp
  simp only [List.getElem_range] at hpi
  subst hpi
  simp only [List.length_range] at hi
  refine ⟨hp.1, hp.2, by omega, fun q hq hq' => ?_⟩
  have := hbefore q hq
  simp only [List.getElem_range, Bool.not_eq_true', Bool.and_eq_false_iff] at this
  rcases this with h | h
  · exact absurd ((pb_iff q).mpr hq'.1) (by simp [h])
  · exact absurd ((pb_iff _).mpr hq'.2) (by simp [h])

theorem goldbach_iff_lw (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N) ↔ ∃ p, lw N = some p := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    have key : ∀ p q, p.Prime → q.Prime → p + q = N → p ≤ q → ∃ r, lw N = some r := by
      intro p q hp hq hpq hle
      unfold lw
      cases h : (List.range (N / 2 + 1)).find? (fun p => pb p && pb (N - p)) with
      | some r => exact ⟨r, rfl⟩
      | none =>
        rw [List.find?_eq_none] at h
        have := h p (List.mem_range.mpr (by omega))
        have hq' : (N - p).Prime := by rwa [show N - p = q by omega]
        simp [(pb_iff p).mpr hp, (pb_iff _).mpr hq'] at this
    rcases le_total p q with hle | hle
    · exact key p q hp hq hpq hle
    · exact key q p hq hp (by omega) hle
  · rintro ⟨p, hp⟩
    obtain ⟨h1, h2, h3, -⟩ := lw_spec hp
    exact ⟨p, N - p, h1, h2, by omega⟩

/-- The ordered Goldbach count. -/
def rOrd (N : ℕ) : Finset ℕ := (Ioo 0 N).filter (fun p => p.Prime ∧ (N - p).Prime)

/-- For even N the ordered count is odd iff N/2 is prime. -/
theorem ordered_parity {N : ℕ} (hN : Even N) :
    (rOrd N).card % 2 = if (N / 2).Prime then 1 else 0 := by
  obtain ⟨m, rfl⟩ := hN
  set N := m + m with hNdef
  set lo := (rOrd N).filter (fun p => p < m)
  set hi := (rOrd N).filter (fun p => m < p)
  set mid := (rOrd N).filter (fun p => p = m)
  have hsplit : (rOrd N).card = lo.card + mid.card + hi.card := by
    have h1 : lo.card + ((rOrd N).filter (fun p => ¬ p < m)).card = (rOrd N).card :=
      Finset.card_filter_add_card_filter_not _
    have h2 : (((rOrd N).filter (fun p => ¬ p < m)).filter (fun p => p = m)).card +
        (((rOrd N).filter (fun p => ¬ p < m)).filter (fun p => ¬ p = m)).card =
        ((rOrd N).filter (fun p => ¬ p < m)).card :=
      Finset.card_filter_add_card_filter_not _
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    have e1 : (rOrd N).filter (fun p => ¬ p < m ∧ p = m) = mid := by
      ext p; simp only [mid, Finset.mem_filter]; constructor
      · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by omega, h'⟩
    have e2 : (rOrd N).filter (fun p => ¬ p < m ∧ ¬ p = m) = hi := by
      ext p; simp only [hi, Finset.mem_filter]; constructor
      · rintro ⟨h, h1, h2⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by omega, by omega⟩
    rw [e1, e2] at h2
    omega
  have hbij : lo.card = hi.card := by
    refine Finset.card_bij' (fun p _ => N - p) (fun p _ => N - p) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [lo, hi, rOrd, Finset.mem_filter, Finset.mem_Ioo] at hp ⊢
      refine ⟨⟨⟨by omega, by omega⟩, hp.1.2.2, ?_⟩, by omega⟩
      rw [show N - (N - p) = p by omega]; exact hp.1.2.1
    · intro p hp
      simp only [lo, hi, rOrd, Finset.mem_filter, Finset.mem_Ioo] at hp ⊢
      refine ⟨⟨⟨by omega, by omega⟩, hp.1.2.2, ?_⟩, by omega⟩
      rw [show N - (N - p) = p by omega]; exact hp.1.2.1
    · intro p hp
      simp only [lo, rOrd, Finset.mem_filter, Finset.mem_Ioo] at hp
      omega
    · intro p hp
      simp only [hi, rOrd, Finset.mem_filter, Finset.mem_Ioo] at hp
      omega
  have hmid : mid.card = if m.Prime then 1 else 0 := by
    split_ifs with hm
    · rw [Finset.card_eq_one]
      refine ⟨m, ?_⟩
      ext p
      simp only [mid, rOrd, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro hp
        rw [hp]
        refine ⟨⟨⟨hm.pos, by have := hm.pos; omega⟩, hm, ?_⟩, rfl⟩
        rw [show m + m - m = m by omega]; exact hm
    · rw [Finset.card_eq_zero]
      ext p
      simp only [mid, rOrd, Finset.mem_filter, Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      rintro ⟨⟨-, hp, -⟩, rfl⟩
      exact hm hp
  rw [show (m + m) / 2 = m by omega, hsplit, hbij, hmid]
  split_ifs <;> omega

/-- Kernel check: the least Goldbach prime is at most 73 on [4, 1000]. -/
theorem lw_table_1000 :
    ∀ k ∈ List.range' 2 499, ∃ p, lw (2 * k) = some p ∧ p ≤ 73 := by
  decide +kernel

theorem lw_992 : lw 992 = some 73 := by decide +kernel

end LeanLab.Routes.R5334

#print axioms LeanLab.Routes.R5334.pb_iff
#print axioms LeanLab.Routes.R5334.lw_spec
#print axioms LeanLab.Routes.R5334.goldbach_iff_lw
#print axioms LeanLab.Routes.R5334.ordered_parity
#print axioms LeanLab.Routes.R5334.lw_table_1000
#print axioms LeanLab.Routes.R5334.lw_992
