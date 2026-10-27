import LeanLab.Ricci1937.Statements

/-!
# P0092 Ricci 1937, the last step of Section 10: the partition (10.1) gives Theorem (A)

Lab proof, unit U-5616, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Page 90 of
papers/P0092.pdf: with j = 210 and k = 32 the partition (10.1) reads `n = p' + ... + p^(64) + w`,
`0 ≤ w ≤ 6719`, "Poichè ogni intero w + 2 si può rappresentare come somma di al più tre numeri
primi, ne segue il Teorema (A)". Here that step is a theorem: the even Goldbach check to 6720 is a
kernel computation, so `theoremA_of_form` has the form as its only hypothesis, which stays cited
as Ricci's Theorem IV. Binary Goldbach is OPEN.
-/

namespace LeanLab.Ricci1937

open LeanLab.SchnirelmannConstant

/-- Ricci's partition (10.1) at `j = 210`, `k = 32`. -/
def RicciForm : Prop :=
  ∃ N, ∀ n, N < n → ∃ l : List ℕ, l.length = 64 ∧ (∀ p ∈ l, p.Prime) ∧ ∃ w, w ≤ 6719 ∧ l.sum + w = n

theorem evenGoldbachUpTo_6720 : EvenGoldbachUpTo 6720 :=
  allEvenGB_sound 6720 (by decide +kernel)

/-- `1 ≤ G(m) ≤ 3` for `2 ≤ m ≤ 6721`, by the kernel. -/
theorem small_atMost3_6721 : ∀ m, 2 ≤ m → m ≤ 6721 → AtMostPrimes 3 m := by
  intro m h2 h
  rcases Nat.even_or_odd m with he | ho
  · exact (atMost2_of_even evenGoldbachUpTo_6720 he (by obtain ⟨k, hk⟩ := he; omega)).mono
      (by norm_num)
  · rcases Nat.lt_or_ge m 7 with h7 | h7
    · obtain ⟨k, rfl⟩ := ho
      have : k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl
      · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
      · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
    · have he : Even (m - 3) := by obtain ⟨k, rfl⟩ := ho; exact ⟨k - 1, by omega⟩
      have := (AtMostPrimes.prime Nat.prime_three).add
        (atMost2_of_even evenGoldbachUpTo_6720 he (by omega))
      rwa [show 3 + (m - 3) = m by omega] at this

/-- **Ricci's step**: the partition (10.1) gives `S ≤ 67`, passing from `n - 2` to `n`. -/
theorem theoremA_of_form (h : RicciForm) : TheoremA := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 2, fun n hn => ?_⟩
  obtain ⟨l, hl, hp, w, hw, hs⟩ := hN (n - 2) (by omega)
  have h64 : AtMostPrimes 64 l.sum := ⟨l, hl.le, hp, rfl⟩
  have h3 := small_atMost3_6721 (w + 2) (by omega) (by omega)
  have := h64.add h3
  rwa [show l.sum + (w + 2) = n by omega] at this

end LeanLab.Ricci1937
