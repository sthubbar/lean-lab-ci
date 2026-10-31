import LeanLab.Ricci1937.CIdentityLower
import LeanLab.Ricci1937.CPrimePairs

/-!
Elementary decomposition of the identity count in Ricci 1937, page 74.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- At most two prime factors means one, a prime, or a product of two primes. -/
lemma almostGT_two_cases {m : ℕ} {R : ℝ} (h : AlmostGT 2 R m) :
    m = 1 ∨ m.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q := by
  have hprod := Nat.prod_primeFactorsList (by have := h.1; omega : m ≠ 0)
  match hl : m.primeFactorsList with
  | [] => left; simpa [hl] using hprod.symm
  | [p] =>
    right; left
    have hp : p.Prime := Nat.prime_of_mem_primeFactorsList (n := m) (by simp [hl])
    have hm : m = p := by simpa [hl] using hprod.symm
    simpa [hm] using hp
  | [p, q] =>
    right; right
    exact ⟨p, q, Nat.prime_of_mem_primeFactorsList (n := m) (by simp [hl]),
      Nat.prime_of_mem_primeFactorsList (n := m) (by simp [hl]), by simpa [hl] using hprod.symm⟩
  | p :: q :: r :: l =>
    have hlen := h.2.1
    simp [hl] at hlen

/-- Large rough values that are not prime belong to the large prime pair block. -/
lemma c1Identity_large_mem_pairs {N m : ℕ} (hN : 4 ≤ N) (hm : m ≤ N)
    (hlarge : (N : ℝ) ^ ((1 : ℝ) / 2) < m)
    (h : AlmostGT 2 ((m : ℝ) ^ ((1 : ℝ) / 3)) m) (hnprime : ¬ m.Prime) :
    m ∈ ricciPrimePairValues N ((1 : ℝ) / 6) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hroot1 : 1 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
  rcases almostGT_two_cases h with hm1 | hprime | ⟨p, q, hp, hq, hprod⟩
  · subst m; linarith
  · exact (hnprime hprime).elim
  have hsmall : (N : ℝ) ^ ((1 : ℝ) / 6) < (m : ℝ) ^ ((1 : ℝ) / 3) := by
    calc
      (N : ℝ) ^ ((1 : ℝ) / 6) =
          ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_mul hNpos.le]
        norm_num
      _ < (m : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_lt_rpow (Real.rpow_nonneg hNpos.le _) hlarge (by norm_num)
  have hp_mem : p ∈ m.primeFactorsList := by
    apply (Nat.mem_primeFactorsList (by have := h.1; omega : m ≠ 0)).mpr
    exact ⟨hp, hprod ▸ dvd_mul_right p q⟩
  have hq_mem : q ∈ m.primeFactorsList := by
    apply (Nat.mem_primeFactorsList (by have := h.1; omega : m ≠ 0)).mpr
    exact ⟨hq, hprod ▸ dvd_mul_left q p⟩
  have hplarge := hsmall.trans (h.2.2 p hp_mem)
  have hqlarge := hsmall.trans (h.2.2 q hq_mem)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hrootpos := Real.rpow_pos_of_pos hNpos ((1 : ℝ) / 6)
  have hprodR : (p : ℝ) * q = m := by exact_mod_cast hprod.symm
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hrootprod : (N : ℝ) ^ (1 - (1 : ℝ) / 6) * (N : ℝ) ^ ((1 : ℝ) / 6) = N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hpmax : (p : ℝ) ≤ (N : ℝ) ^ (1 - (1 : ℝ) / 6) := by
    nlinarith
  apply mem_biUnion.mpr
  refine ⟨p, mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_, hp⟩, hplarge.le, hpmax⟩,
    mem_image.mpr ⟨q, Nat.mem_primesLE.mpr ⟨?_, hq⟩, hprod.symm⟩⟩
  · have : p ≤ m := hprod ▸ Nat.le_mul_of_pos_right p hq.pos
    exact this.trans hm
  · apply (Nat.le_div_iff_mul_le hp.pos).mpr
    nlinarith

/-- Separate small values, primes, and large prime products. -/
theorem c1Identity_count_le (N : ℕ) (hN : 4 ≤ N) :
    c1IdentityCount N ≤ ⌊(N : ℝ) ^ ((1 : ℝ) / 2)⌋₊ + N.primeCounting +
      #(ricciPrimePairValues N ((1 : ℝ) / 6)) := by
  have hsub : {m ∈ Icc (1 : ℕ) N | AlmostGT 2 (((m : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) m} ⊆
      Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 2)⌋₊ ∪ Nat.primesLE N ∪
        ricciPrimePairValues N ((1 : ℝ) / 6) := by
    intro m hm
    rcases mem_filter.mp hm with ⟨hmI, h⟩
    by_cases hsmall : m ≤ ⌊(N : ℝ) ^ ((1 : ℝ) / 2)⌋₊
    · exact mem_union_left _ (mem_union_left _ (mem_Icc.mpr ⟨(mem_Icc.mp hmI).1, hsmall⟩))
    by_cases hp : m.Prime
    · exact mem_union_left _ (mem_union_right _ (Nat.mem_primesLE.mpr ⟨(mem_Icc.mp hmI).2, hp⟩))
    apply mem_union_right
    apply c1Identity_large_mem_pairs hN (mem_Icc.mp hmI).2 _ h hp
    have hroot0 := Real.rpow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) ((1 : ℝ) / 2)
    exact lt_of_not_ge (fun hmR => hsmall ((Nat.le_floor_iff hroot0).mpr hmR))
  calc
    c1IdentityCount N ≤ #(Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 2)⌋₊ ∪ Nat.primesLE N ∪
        ricciPrimePairValues N ((1 : ℝ) / 6)) := card_le_card hsub
    _ ≤ #(Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 2)⌋₊ ∪ Nat.primesLE N) +
        #(ricciPrimePairValues N ((1 : ℝ) / 6)) := card_union_le _ _
    _ ≤ (#(Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 2)⌋₊) + #(Nat.primesLE N)) +
        #(ricciPrimePairValues N ((1 : ℝ) / 6)) := Nat.add_le_add_right (card_union_le _ _) _
    _ = _ := by simp [Nat.primesLE_card_eq_primeCounting]

example : c1IdentityCount 4 ≤ ⌊(4 : ℝ) ^ ((1 : ℝ) / 2)⌋₊ +
    (4 : ℕ).primeCounting + #(ricciPrimePairValues 4 ((1 : ℝ) / 6)) :=
  c1Identity_count_le 4 (by norm_num)

example : (25 : ℕ) = 1 ∨ (25 : ℕ).Prime ∨
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 25 = p * q := by
  apply almostGT_two_cases (R := 2)
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show Nat.primeFactorsList 25 = [5, 5] by norm_num]
    simp
  · intro p hp
    rw [show Nat.primeFactorsList 25 = [5, 5] by norm_num] at hp
    simp at hp
    subst p
    norm_num

end
end LeanLab.Ricci1937
