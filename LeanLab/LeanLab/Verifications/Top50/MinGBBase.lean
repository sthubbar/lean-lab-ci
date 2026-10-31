/-
Base of the q ≤ 1789 chain, U-0352: the 10^6 check with the small prime bounded by 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.SmallGB

namespace LeanLab.Verifications.Top50.Bits

open LeanLab.Verifications.Top50

theorem take278_le : ∀ q ∈ P10k.take 278, q ≤ 1789 := by
  have h : (P10k.take 278).all (fun q => decide (q ≤ 1789)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem take99_le1789 : ∀ q ∈ P10k.take 99, q ≤ 1789 := by
  have h : (P10k.take 99).all (fun q => decide (q ≤ 1789)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

/-- The 10^6 check with the small prime at most 1789. -/
theorem msmall_1e6 : SmallGBUpTo 1789 1000000 := by
  intro n hn h4 hnB
  have he : 2 ∣ n - 4 := by obtain ⟨k, rfl⟩ := hn; exact ⟨k - 2, by omega⟩
  have h1 := testBit_em h4 hnB he
  rw [← check_1e6, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨q, hq, hqn, hp⟩ := of_gm _ _ n h1.2
  exact ⟨q, take_prime 99 q hq, take99_le1789 q hq, hqn, prime_of_pm (by norm_num) hp⟩

end LeanLab.Verifications.Top50.Bits
