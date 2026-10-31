/-
Goldbach partitions with a small prime, for the kernel windows.
SmallGBUpTo N B: every even n with 4 ≤ n ≤ B is q + p with q, p prime and q ≤ N.
The window checks of BitSieve.lean and BitSieve2.lean already give a q from the list Q, so the
same windows prove this stronger statement; it bounds minGB, the least prime of a Goldbach
partition used by Granville, van de Lune and te Riele, P0042.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitUpTo1e6
import LeanLab.Verifications.Top50.BitSieve2
import LeanLab.Verifications.Statements

namespace LeanLab.Verifications.Top50.Bits

open LeanLab.Verifications.Top50

/-- Every even `n` with `4 ≤ n ≤ B` is `q + p` with `q, p` prime and `q ≤ N`. -/
def SmallGBUpTo (N B : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n ≤ B → ∃ q, q.Prime ∧ q ≤ N ∧ q ≤ n ∧ (n - q).Prime

theorem take280_le : ∀ q ∈ P10k.take 280, q ≤ 1811 := by
  have h : (P10k.take 280).all (fun q => decide (q ≤ 1811)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem take99_le : ∀ q ∈ P10k.take 99, q ≤ 1811 := by
  have h : (P10k.take 99).all (fun q => decide (q ≤ 1811)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

/-- The 10^6 check with the small prime kept. -/
theorem small_1e6 : SmallGBUpTo 1811 1000000 := by
  intro n hn h4 hnB
  have he : 2 ∣ n - 4 := by obtain ⟨k, rfl⟩ := hn; exact ⟨k - 2, by omega⟩
  have h1 := testBit_em h4 hnB he
  rw [← check_1e6, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨q, hq, hqn, hp⟩ := of_gm _ _ n h1.2
  exact ⟨q, take_prime 99 q hq, take99_le q hq, hqn, prime_of_pm (by norm_num) hp⟩

/-- Extend `SmallGBUpTo N a` by one window `[A, B]` with `A = a + 2`, the start as a numeral. -/
theorem small_extend2 {N lo W a A B : ℕ} {Q : List ℕ} (ha : SmallGBUpTo N a) (hae : 2 ∣ a)
    (hA : a + 2 = A) (h2 : 2 ≤ lo) (hW : lo + W ≤ B2) (hlo : lo ≤ A) (hQ : ∀ q ∈ Q, q.Prime)
    (hQN : ∀ q ∈ Q, q ≤ N)
    (h : wem lo A B &&& gm (wpm2 lo W) Q = wem lo A B) : SmallGBUpTo N B := by
  subst hA
  intro n hn h4 hnB
  by_cases hna : n ≤ a
  · exact ha n hn h4 hna
  · have hn2 : a + 2 ≤ n := by
      obtain ⟨k, hk⟩ := hn
      obtain ⟨i, hi⟩ := hae
      omega
    have he : 2 ∣ n - (a + 2) :=
      Nat.dvd_sub (even_iff_two_dvd.mp hn) (Nat.dvd_add hae (dvd_refl 2))
    have h1 := testBit_wem hlo hn2 hnB he
    rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
    obtain ⟨q, hq, hqn, hp⟩ := of_gm _ Q _ h1.2
    have hpr := prime_of_wpm2 h2 hW hp
    refine ⟨q, hQ q hq, hQN q hq, by omega, ?_⟩
    rw [show n - q = lo + (n - lo - q) by omega]
    exact hpr

theorem small_mono {N a b : ℕ} (h : SmallGBUpTo N b) (hab : a ≤ b) : SmallGBUpTo N a :=
  fun n hn h4 hna => h n hn h4 (le_trans hna hab)

theorem upTo_of_small {N B : ℕ} (h : SmallGBUpTo N B) : EvenGoldbachUpTo B := by
  intro n hn h4 hnB
  obtain ⟨q, hq, -, hqn, hp⟩ := h n hn h4 hnB
  exact ⟨q, n - q, hq, hp, by omega⟩

/-- A small Goldbach partition bounds `minGB`, the least prime of a partition. -/
theorem minGB_le_of_small {N B : ℕ} (h : SmallGBUpTo N B) {n : ℕ} (hn : Even n) (h4 : 4 ≤ n)
    (hnB : n ≤ B) : LeanLab.Verifications.minGB n ≤ N := by
  obtain ⟨q, hq, hqN, -, hp⟩ := h n hn h4 hnB
  have hex : ∃ p, p.Prime ∧ (n - p).Prime := ⟨q, hq, hp⟩
  unfold LeanLab.Verifications.minGB
  rw [dif_pos hex]
  exact le_trans (Nat.find_min' hex ⟨hq, hp⟩) hqN

end LeanLab.Verifications.Top50.Bits
