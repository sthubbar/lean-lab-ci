/-
I-0065, shared machinery: a kernel check that minGB n ≤ B on a block of even numbers.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.FastCheck

namespace LeanLab.Verifications.Top50.Fast

open LeanLab.Verifications LeanLab.Verifications.Top50

/-- A witness `q ≤ B` bounds the least Goldbach prime. -/
theorem minGB_le_of {n q B : ℕ} (hq : q.Prime) (hnq : (n - q).Prime) (hqB : q ≤ B) :
    minGB n ≤ B := by
  have hex : ∃ p, p.Prime ∧ (n - p).Prime := ⟨q, hq, hnq⟩
  unfold minGB
  rw [dif_pos hex]
  exact le_trans (Nat.find_min' hex ⟨hq, hnq⟩) hqB

/-- Try `q ∈ L` with `q ≤ B` until `n - q` passes `td`. -/
def findQb (n B : ℕ) : List ℕ → Bool
  | [] => false
  | q :: t => (q ≤ B && q + 2 ≤ n && td (n - q) P10k) || findQb n B t

theorem findQb_sound (n B : ℕ) (hn : n < 10 ^ 8) : ∀ L : List ℕ, (∀ q ∈ L, q.Prime) →
    findQb n B L = true → minGB n ≤ B := by
  intro L
  induction L with
  | nil => intro _ h; simp [findQb] at h
  | cons a t ih =>
    intro hL h
    simp only [findQb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨h0, h1⟩, h2⟩ | h
    · exact minGB_le_of (hL a (by simp)) (prime_of_td (by omega) (by omega) h2) h0
    · exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) h

def allGBb (B : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, n => findQb n B P10k && allGBb B fuel (n + 2)

theorem allGBb_sound (B : ℕ) : ∀ fuel n, n + 2 * fuel ≤ 10 ^ 8 → allGBb B fuel n = true →
    ∀ k, k < fuel → minGB (n + 2 * k) ≤ B := by
  intro fuel
  induction fuel with
  | zero => intro n _ _ k hk; omega
  | succ f ih =>
    intro n hb h k hk
    simp only [allGBb, Bool.and_eq_true] at h
    rcases k with _ | k
    · simpa using findQb_sound n B (by omega) P10k P10k_prime h.1
    · have := ih (n + 2) (by omega) h.2 k (by omega)
      rwa [show n + 2 + 2 * k = n + 2 * (k + 1) by ring] at this

/-- A checked block in range form: even `n` with `a ≤ n < a + 2 fuel`, `a` even. -/
theorem block_range {B a fuel : ℕ} (ha : Even a) (hb : a + 2 * fuel ≤ 10 ^ 8)
    (h : allGBb B fuel a = true) :
    ∀ n, Even n → a ≤ n → n < a + 2 * fuel → minGB n ≤ B := by
  intro n hn h1 h2
  obtain ⟨j, rfl⟩ := hn
  obtain ⟨i, rfl⟩ := ha
  have hk : j + j = i + i + 2 * (j - i) := by omega
  rw [hk]
  exact allGBb_sound B fuel (i + i) hb h (j - i) (by omega)

end LeanLab.Verifications.Top50.Fast
