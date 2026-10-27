/-
Almost equal ternary Goldbach with window √n, a kernel-checked small range.
Our own numerical test next to P0028 Matomaki-Maynard-Shao 2016, see IDEAS I-0014.
Every odd n with 7 ≤ n ≤ N is p1 + p2 + p3, primes, each within √n of n/3.
This says nothing about large n; Matomaki-Maynard-Shao need θ > 11/20 and n large.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Ternary.AlmostEqual

namespace LeanLab.Ternary

/-- `x` lies within `√n` of `n/3`, tested as `(3x − n)² ≤ 9n`. -/
def inW (n x : ℕ) : Bool :=
  (if n ≤ 3 * x then (3 * x - n) ^ 2 else (n - 3 * x) ^ 2) ≤ 9 * n

theorem inW_sound {n x : ℕ} (h : inW n x = true) :
    |(x : ℝ) - n / 3| ≤ Real.sqrt n := by
  apply Real.abs_le_sqrt
  simp only [inW, decide_eq_true_eq] at h
  have key : ((3 * (x : ℝ) - n)) ^ 2 ≤ 9 * n := by
    split_ifs at h with h3
    · have : ((3 * x - n : ℕ) : ℝ) = 3 * (x : ℝ) - n := by push_cast [Nat.cast_sub h3]; ring
      rw [← this]; exact_mod_cast h
    · push Not at h3
      have : ((n - 3 * x : ℕ) : ℝ) = n - 3 * (x : ℝ) := by
        push_cast [Nat.cast_sub h3.le]; ring
      have e : (3 * (x : ℝ) - n) ^ 2 = ((n - 3 * x : ℕ) : ℝ) ^ 2 := by rw [this]; ring
      rw [e]; exact_mod_cast h
  nlinarith [key]

/-- Search `q = q₀, q₀ + 1, …` for primes `q`, `r = n − p − q`, both in the window. -/
def findQ (n p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, q =>
      (decide (p + q ≤ n) && inW n q && inW n (n - p - q) && primeB q && primeB (n - p - q))
        || findQ n p f (q + 1)

/-- Search `p = p₀, p₀ + 1, …`. -/
def findP (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, p =>
      (decide (p ≤ n) && inW n p && primeB p &&
          findQ n p (2 * Nat.sqrt n + 3) ((n - 3 * Nat.sqrt n) / 3))
        || findP n f (p + 1)

/-- The check for one `n`, searching the window from its left end. -/
def aeCheck (n : ℕ) : Bool :=
  findP n (2 * Nat.sqrt n + 3) ((n - 3 * Nat.sqrt n) / 3)

theorem findQ_sound (n p : ℕ) (hp : p.Prime) (hpw : |(p : ℝ) - n / 3| ≤ Real.sqrt n) :
    ∀ f q, findQ n p f q = true → IsAlmostEqualTernary n (Real.sqrt n) := by
  intro f
  induction f with
  | zero => intro q h; simp [findQ] at h
  | succ k ih =>
    intro q h
    simp only [findQ, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨hle, hq⟩, hr⟩, hqp⟩, hrp⟩ | h
    · exact ⟨p, q, n - p - q, hp, primeB_sound hqp, primeB_sound hrp, by omega,
        hpw, inW_sound hq, inW_sound hr⟩
    · exact ih (q + 1) h

theorem findP_sound (n : ℕ) : ∀ f p, findP n f p = true →
    IsAlmostEqualTernary n (Real.sqrt n) := by
  intro f
  induction f with
  | zero => intro p h; simp [findP] at h
  | succ k ih =>
    intro p h
    simp only [findP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨-, hw⟩, hpp⟩, hq⟩ | h
    · exact findQ_sound n p (primeB_sound hpp) (inW_sound hw) _ _ hq
    · exact ih (p + 1) h

theorem aeCheck_sound {n : ℕ} (h : aeCheck n = true) :
    IsAlmostEqualTernary n (Real.sqrt n) :=
  findP_sound n _ _ h

/-- Check every odd `n` with `a ≤ n < a + len`, `7 ≤ a`. -/
def aeRange (a : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => (if (a + len) % 2 = 1 then aeCheck (a + len) else true) && aeRange a len

theorem aeRange_sound (a : ℕ) : ∀ len, aeRange a len = true →
    ∀ n, a ≤ n → n < a + len → n % 2 = 1 → IsAlmostEqualTernary n (Real.sqrt n) := by
  intro len
  induction len with
  | zero => intro _ n h1 h2; omega
  | succ k ih =>
    intro h n h1 h2 ho
    simp only [aeRange, Bool.and_eq_true] at h
    obtain ⟨h3, h4⟩ := h
    rcases Nat.lt_or_ge n (a + k) with hlt | hge
    · exact ih h4 n h1 hlt ho
    · have hn : n = a + k := by omega
      subst hn
      simp only [ho, ite_true] at h3
      exact aeCheck_sound h3

end LeanLab.Ternary
