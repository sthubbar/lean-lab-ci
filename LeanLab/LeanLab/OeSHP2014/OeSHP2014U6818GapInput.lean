/-
U-6818, P0005 Oliveira e Silva, Herzog, Pardi 2014: the lab's cited gap input
`GoldbachGaps.Sumset.GapBound1476`, every interval (a, a + 1476] with 2 ≤ a and
a + 1476 ≤ 4·10^18 holds a prime, is a consequence of the paper's Table 8 statement as the
lab cites it in `Verifications.OeSHP.maxGap`: consecutive primes p < q with q ≤ 4·10^18
differ by at most 1476. The bridge needs one extra fact, a prime close below 4·10^18, so
that the interval never runs past the searched range: 3999999999999999887 = 4·10^18 - 113
is prime, kernel checked here by a Lucas certificate. So GapBound1476 is CONDITIONAL ON the
paper's maximal gap statement only, with nothing stronger smuggled in.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Pratt
import LeanLab.GoldbachGaps.Sumset

namespace LeanLab.OeSHP2014.GapInput

open LeanLab.Verifications.Pratt

/-- The paper's Table 8 claim in the form `Verifications.OeSHP.maxGap` states it. -/
def MaxGap1476 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q → q ≤ 4 * 10 ^ 18 →
    (∀ r, p < r → r < q → ¬ r.Prime) → q - p ≤ 1476

theorem p2712263549 : Nat.Prime 2712263549 := by
  refine pratt 2712263549 2 [(2, 2), (157, 1), (4318891, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Nat.prime_two
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p181818181818181813 : Nat.Prime 181818181818181813 := by
  refine pratt 181818181818181813 5
    [(2, 2), (3, 1), (29, 1), (192631, 1), (2712263549, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2712263549

/-- The largest prime below 4·10^18 is at most 113 below it; this one is prime. -/
theorem p_top : Nat.Prime 3999999999999999887 := by
  refine pratt 3999999999999999887 5 [(2, 1), (11, 1), (181818181818181813, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Nat.prime_two
  · exact pB (by decide +kernel)
  · exact p181818181818181813

/-- Natural-number core: below 4·10^18 - 1476, the next prime after m is within 1476 of m. -/
theorem next_prime_within (hG : MaxGap1476) (m : ℕ) (hm2 : 2 ≤ m)
    (hm : m + 1476 ≤ 4 * 10 ^ 18) : ∃ q : ℕ, q.Prime ∧ m < q ∧ q ≤ m + 1476 := by
  classical
  -- q, the least prime above m; it exists below the top prime
  have hexq : ∃ q, q.Prime ∧ m < q := ⟨3999999999999999887, p_top, by omega⟩
  let q := Nat.find hexq
  have hq : q.Prime ∧ m < q := Nat.find_spec hexq
  have hqmin : ∀ r, r.Prime → m < r → q ≤ r := fun r hr hmr => Nat.find_min' hexq ⟨hr, hmr⟩
  have hqtop : q ≤ 4 * 10 ^ 18 := le_trans (hqmin _ p_top (by omega)) (by norm_num)
  -- p, the greatest prime at most m
  have hexp : ∃ k, (m - k).Prime ∧ k ≤ m := ⟨m - 2, by
    rw [show m - (m - 2) = 2 by omega]; exact Nat.prime_two, by omega⟩
  let k := Nat.find hexp
  have hk : (m - k).Prime ∧ k ≤ m := Nat.find_spec hexp
  have hkmin : ∀ j, (m - j).Prime → j ≤ m → k ≤ j :=
    fun j hj hjm => Nat.find_min' hexp ⟨hj, hjm⟩
  have hgap := hG (m - k) q hk.1 hq.1 (by omega) hqtop (by
    intro r hr1 hr2 hrp
    by_cases hrm : r ≤ m
    · have := hkmin (m - r) (by rw [show m - (m - r) = r by omega]; exact hrp) (by omega)
      omega
    · have := hqmin r hrp (by omega)
      omega)
  exact ⟨q, hq.1, hq.2, by omega⟩

/-- `GapBound1476` follows from the paper's maximal gap statement and the top prime. -/
theorem gapBound1476_of_maxGap (hG : MaxGap1476) : LeanLab.GoldbachGaps.Sumset.GapBound1476 := by
  intro a ha hab
  set m := ⌊a⌋₊ with hmdef
  have ha0 : 0 ≤ a := by linarith
  have hm_le : (m : ℝ) ≤ a := Nat.floor_le ha0
  have hm_lt : a < m + 1 := Nat.lt_floor_add_one a
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ m := by
      have h2 : ((2 : ℕ) : ℝ) ≤ a := by exact_mod_cast ha
      exact_mod_cast Nat.le_floor h2
    exact_mod_cast this
  have hmN : m + 1476 ≤ 4 * 10 ^ 18 := by
    have : (m : ℝ) + 1476 ≤ 4 * 10 ^ 18 := by linarith
    exact_mod_cast this
  obtain ⟨q, hq, hmq, hqm⟩ := next_prime_within hG m hm2 hmN
  refine ⟨q, hq, ?_, ?_⟩
  · have : (m : ℝ) + 1 ≤ q := by exact_mod_cast hmq
    linarith
  · have : (q : ℝ) ≤ m + 1476 := by exact_mod_cast hqm
    linarith

/-- The lab's cited statement `Verifications.OeSHP.maxGap` has exactly this shape. -/
theorem maxGap1476_iff_oeshp :
    MaxGap1476 ↔ ∀ p q, p.Prime → q.Prime → p < q → q ≤ 4 * 10 ^ 18 →
      (∀ r, p < r → r < q → ¬ r.Prime) → q - p ≤ 1476 := Iff.rfl

end LeanLab.OeSHP2014.GapInput

#print axioms LeanLab.OeSHP2014.GapInput.p_top
#print axioms LeanLab.OeSHP2014.GapInput.gapBound1476_of_maxGap
