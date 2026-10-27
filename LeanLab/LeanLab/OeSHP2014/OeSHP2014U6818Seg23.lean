/-
U-6818, P0005, Table 4 record gap 23: SmallGBUpTo for the row's p up to the next row,
windows of at most 2000000, part of OeSHP2014U6818Exact1e8.lean. AI-written Lean code, Claude,
2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Exact1e7

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem small_bound_mono {N N' B : ℕ} (h : SmallGBUpTo N B) (hN : N ≤ N') : SmallGBUpTo N' B :=
  fun n hn h4 hnB => by
    obtain ⟨q, hq, hqN, hqn, hp⟩ := h n hn h4 hnB
    exact ⟨q, hq, hqN.trans hN, hqn, hp⟩

/-- Extend `SmallGBUpTo N a` by one window `[A, B]`, `A = a + 2`, sieve `wpm lo W`. -/
theorem small_extend_w {N lo W a A B : ℕ} {Q : List ℕ} (ha : SmallGBUpTo N a) (hae : 2 ∣ a)
    (hA : a + 2 = A) (h2 : 2 ≤ lo) (hW : lo + W ≤ 10 ^ 8) (hlo : lo ≤ A) (hQ : ∀ q ∈ Q, q.Prime)
    (hQN : ∀ q ∈ Q, q ≤ N)
    (h : wem lo A B &&& gm (wpm lo W) Q = wem lo A B) : SmallGBUpTo N B := by
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
    have hpr := prime_of_wpm h2 hW hp
    refine ⟨q, hQ q hq, hQN q hq, by omega, ?_⟩
    rw [show n - q = lo + (n - lo - q) by omega]
    exact hpr

theorem take_le_23 : ∀ q ∈ P10k.take 133, q ≤ 751 := by
  have h : (P10k.take 133).all (fun q => decide (q ≤ 751)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem window_23_0 : wem 9998802 10000002 10759920 &&& gm (wpm 9998802 761118) (P10k.take 133) =
    wem 9998802 10000002 10759920 := by
  decide +kernel

theorem seg_23_0 : SmallGBUpTo 751 10759920 :=
  small_extend_w (a := 10000000) (A := 10000002) (lo := 9998802) (W := 761118) Exact1e7.seg_23
    ⟨5000000, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 133) take_le_23 window_23_0

theorem seg_23 : SmallGBUpTo 751 10759920 := seg_23_0


end LeanLab.OeSHP2014.Exact1e8
