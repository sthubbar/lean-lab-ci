import Mathlib
import LeanLab.Common.Goldbach

/-!
# R-5230, T3 MOONSHOT: balanced Goldbach, both primes near `N/2`

Unit U-6652, CLOUD 20261020T1717Z-cloud47. AI wrote this file.

Route: write `N = 2m` and ask for `k` with `m - k` and `m + k` both prime; `d(N)` is the least
such `k`. Binary Goldbach for `N` is exactly `d(N) < m`, `goldbach_iff_balanced`, so the route
asks for the stronger, local statement `d(N) ≤ H(N)` with `H` small, and reads binary Goldbach
as a statement about the reducible quadratic `m² - k² = (m - k)(m + k)` having a value with
exactly two prime factors, one on each linear factor, for some `k < m`.
* `balanced_pair_goldbach`: a balanced pair at any `k ≤ m - 2` is a Goldbach representation;
* `goldbach_iff_balanced`: for even `N = 2m ≥ 4`, Goldbach for `N` iff some `k < m` is balanced;
* `balanced_upto_3380`: kernel checked, every `m` with `3 ≤ m ≤ 1690`, that is every even
  `6 ≤ N ≤ 3380`, has a balanced pair with `k ≤ 117`, the record `d(2228) = 117` of the
  numerics, Routes/numerics/r5230_U6652.out.
Binary Goldbach is OPEN; this route is a reformulation, its status is a barrier map.
-/

namespace LeanLab.Routes.R5230

/-- `m - k` and `m + k` are both prime. -/
def Balanced (m k : ℕ) : Prop := (m - k).Prime ∧ (m + k).Prime

/-- A balanced pair is a Goldbach representation of `2m`. -/
theorem balanced_pair_goldbach {m k : ℕ} (hk : k ≤ m) (h : Balanced m k) :
    IsGoldbachSum (2 * m) :=
  ⟨m - k, m + k, h.1, h.2, by omega⟩

/-- **Goldbach for `2m` is a balanced pair at some `k < m`.** -/
theorem goldbach_iff_balanced (m : ℕ) :
    IsGoldbachSum (2 * m) ↔ ∃ k < m, Balanced m k := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    rcases le_total p q with hle | hle
    · refine ⟨m - p, ?_, ?_, ?_⟩
      · have := hq.two_le; have := hp.two_le; omega
      · have e : m - (m - p) = p := by omega
        rw [e]; exact hp
      · have e : m + (m - p) = q := by omega
        rw [e]; exact hq
    · refine ⟨m - q, ?_, ?_, ?_⟩
      · have := hq.two_le; have := hp.two_le; omega
      · have e : m - (m - q) = q := by omega
        rw [e]; exact hq
      · have e : m + (m - q) = p := by omega
        rw [e]; exact hp
  · rintro ⟨k, hk, h⟩
    exact balanced_pair_goldbach hk.le h

/-! ### The kernel check -/

/-- Search `k = 0, 1, …, K` for a balanced pair, Boolean. -/
def balB (m : ℕ) : ℕ → Bool
  | 0 => primeB m && primeB m
  | K + 1 => (primeB (m - (K + 1)) && primeB (m + (K + 1))) || balB m K

theorem balB_sound (m : ℕ) : ∀ K, balB m K = true → ∃ k ≤ K, Balanced m k := by
  intro K
  induction K with
  | zero =>
    intro h
    simp only [balB, Bool.and_self] at h
    exact ⟨0, le_rfl, by simpa using primeB_sound h, by simpa using primeB_sound h⟩
  | succ K ih =>
    intro h
    simp only [balB, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨K + 1, le_rfl, primeB_sound h1, primeB_sound h2⟩
    · obtain ⟨k, hk, hb⟩ := ih h
      exact ⟨k, by omega, hb⟩

/-- Check every `m` from `3` to `M` with window `K`. -/
def allBal (K : ℕ) : ℕ → Bool
  | 0 => true
  | M + 1 => (if 3 ≤ M + 1 then balB (M + 1) K else true) && allBal K M

theorem allBal_sound (K : ℕ) : ∀ M, allBal K M = true →
    ∀ m, 3 ≤ m → m ≤ M → ∃ k ≤ K, Balanced m k := by
  intro M
  induction M with
  | zero => intro _ m h3 hm; omega
  | succ M ih =>
    intro h m h3 hm
    simp only [allBal, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases Nat.lt_or_ge m (M + 1) with hlt | hge
    · exact ih h2 m h3 (by omega)
    · have e : m = M + 1 := by omega
      subst e
      rw [if_pos h3] at h1
      exact balB_sound _ K h1

/-- **Every even `6 ≤ N ≤ 3380` is `p + q` with `|p - q| ≤ 234`**, kernel checked. -/
theorem balanced_upto_3380 : ∀ m, 3 ≤ m → m ≤ 1690 → ∃ k ≤ 117, Balanced m k :=
  allBal_sound 117 1690 (by decide +kernel)

/-- The same, as Goldbach representations. -/
theorem goldbach_balanced_upto_3380 (m : ℕ) (h3 : 3 ≤ m) (hm : m ≤ 1690) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * m ∧ q ≤ p + 234 := by
  obtain ⟨k, hk, h1, h2⟩ := balanced_upto_3380 m h3 hm
  have hkm : k ≤ m := by have := h1.two_le; omega
  exact ⟨m - k, m + k, h1, h2, by omega, by omega⟩

end LeanLab.Routes.R5230
