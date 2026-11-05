/-
Supply split for DecompJ1133.large_even_upper. The sealed file is unchanged.
Ramaré 1995 Section 9 pp. 703 to 704 supplies the counting hypothesis.
The existing Theorem91 and HypB modules supply the additive argument and the high block.
Only the explicit counting hypothesis remains open. It does not assert representations
of every large integer. The low block below removes the finite Goldbach input here.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Ramare1995.HypB
import LeanLab.Ramare1995.Theorem91

namespace LeanLab.Ramare1995.Decomp369b
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

/-- The first finite block in hypothesis b on pp. 701 and 704 needs only Goldbach through 84.
Explicit prime pairs remove the much larger cited finite Goldbach input from this block. -/
theorem low_block : ∀ i : ℕ, i ≤ 39 → i ∈ 𝒜 := by
  intro i hi
  change IsGoldbachSum (2 * i + 6)
  interval_cases i
  · exact ⟨3, 3, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 5, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 7, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 7, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 11, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 13, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 13, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 17, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 19, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 19, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 23, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 23, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 23, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 29, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 31, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 31, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 31, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 37, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 37, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 41, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 43, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 43, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 47, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 47, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 47, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 53, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 53, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 53, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 59, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 61, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 61, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 61, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 67, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 67, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 71, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 73, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 73, by norm_num, by norm_num, rfl⟩
  · exact ⟨7, 73, by norm_num, by norm_num, rfl⟩
  · exact ⟨3, 79, by norm_num, by norm_num, rfl⟩
  · exact ⟨5, 79, by norm_num, by norm_num, rfl⟩

/-- The p. 704 count bound alone suffices for the large range.
CONDITIONAL ON that bound. The additive theorem and both finite blocks are proved. -/
theorem large_even_of_count
    (hA : ∀ m : ℕ, n₀ ≤ m → (7 / 20 : ℝ) * m + 1560 ≤ cnt 𝒜 m) :
    ∀ N : ℕ, Even N → 6 * n₀ + 18 ≤ N → AtMostPrimes 6 N := by
  intro N hN hle
  obtain ⟨k, hk⟩ := hN
  have h0 : (0 : ℕ) ∈ 𝒜 := ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
  have hA' : ∀ m : ℕ, n₀ ≤ m →
      (7 / 20 : ℝ) * m + (39 * (39 + 1) / 2 : ℝ) * ((3 : ℝ) - 1) ≤ cnt 𝒜 m := by
    intro m hm
    convert hA m hm using 1 <;> norm_num
  obtain ⟨l, hl, hmem, hs⟩ := Theorem91.theorem91 𝒜 (7 / 20) 3 39 n₀
    (by norm_num) h0 hA' low_block HypB.hypBHigh hypC (k - 9) (by omega)
  have h1 := atMost_of_list l hmem
  have h2 := six_mul (3 - l.length)
  have hsum := h1.add h2
  rw [hs] at hsum
  have heq : 2 * (k - 9) + 6 * l.length + 6 * (3 - l.length) = N := by
    omega
  rw [heq] at hsum
  exact hsum.mono (by omega)

/-- The remark after Theorem 9.1 on p. 701 requires density greater than 1 divided by H.
For H greater than one this follows from hypothesis c for every finite K. -/
theorem density_required (H K : ℕ) (hH : 1 < H) (σ : ℝ)
    (hc : (K : ℝ) + H ≤ (K + 1) * H * σ) : 1 / (H : ℝ) < σ := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hH1 : (1 : ℝ) < H := by exact_mod_cast hH
  by_contra h
  push Not at h
  have hm := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((K : ℝ) + 1) * H by positivity)
  have he : ((K : ℝ) + 1) * H * (1 / (H : ℝ)) = K + 1 := by
    field_simp
  rw [he] at hm
  linarith

/-- The density restriction in the p. 701 remark is exactly the obstruction to choosing K.
This concerns hypothesis c alone and asserts no counting or prime distribution bound. -/
theorem hypC_solvable_iff (H : ℕ) (hH : 1 < H) (σ : ℝ) :
    (∃ K : ℕ, (K : ℝ) + H ≤ (K + 1) * H * σ) ↔ 1 / (H : ℝ) < σ := by
  constructor
  · rintro ⟨K, hc⟩
    exact density_required H K hH σ hc
  · intro hσ
    have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    have hd : 0 < (H : ℝ) * σ - 1 := by
      have h := (div_lt_iff₀ hH0).mp hσ
      nlinarith
    obtain ⟨K, hK⟩ := exists_nat_ge ((H : ℝ) / ((H : ℝ) * σ - 1))
    have hm := (div_le_iff₀ hd).mp hK
    exact ⟨K, by nlinarith⟩

/-- For H equal to 3, hypothesis c on p. 701 forces density strictly above one third.
This diagnoses why the existing weak density cannot replace the paper input. -/
theorem three_summands_requires_density (K : ℕ) (σ : ℝ)
    (hc : (K : ℝ) + 3 ≤ (K + 1) * 3 * σ) : 1 / 3 < σ := by
  by_contra h
  push Not at h
  have hm := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((K : ℝ) + 1) * 3 by positivity)
  nlinarith

/-- No choice of K makes the weak elementary coefficient satisfy hypothesis c for H = 3.
The scalar density is twice the existing dyadic coefficient 1 divided by 10^8. -/
theorem weak_density_not_hypC (K : ℕ) :
    ¬ ((K : ℝ) + 3 ≤ (K + 1) * 3 * (2 / 10 ^ 8 : ℝ)) := by
  intro hc
  have h := three_summands_requires_density K _ hc
  norm_num at h

/-- The same weak density needs more than fifty million additive summands in hypothesis c.
This is an obstruction to that use of the weak bound, not to the six prime theorem. -/
theorem weak_density_summand_lower_bound (H K : ℕ) (hH : 1 < H)
    (hc : (K : ℝ) + H ≤ (K + 1) * H * (2 / 10 ^ 8 : ℝ)) : 50000000 < H := by
  have h := density_required H K hH _ hc
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hm := (div_lt_iff₀ hH0).mp h
  have hr : (50000000 : ℝ) < H := by nlinarith
  exact_mod_cast hr

/-- The existing dyadic proof on p. 704 supplies the open count bound from its cited inputs.
CONDITIONAL ON Theorem 2 and finite Goldbach through 2 times 10^10. -/
theorem count_lower_of_inputs (h2 : Theorem2) (hG : EvenGoldbachUpTo (2 * 10 ^ 10))
    (m : ℕ) (hm : n₀ ≤ m) : (7 / 20 : ℝ) * m + 1560 ≤ cnt 𝒜 m := by
  have h := Section9.hypA h2 hG m hm
  norm_num at h
  exact h

/-- LEAF. Ramaré 1995 p. 704, the unnumbered display after the use of Theorem 2.
For m at least n₀, the count of elements of A through m is at least 7m/20 plus 1560.
Here H is 3 and K is 39, as fixed on p. 703. This is hypothesis a of Theorem 9.1,
not the conclusion that every even integer is a sum of six primes. -/
theorem count_lower (m : ℕ) (hm : n₀ ≤ m) :
    (7 / 20 : ℝ) * m + 1560 ≤ cnt 𝒜 m := by
  sorry

/-- Supply assembly of the exact upper leaf statement.
CONDITIONAL ON count_lower. No sorry of its own. -/
theorem large_even_upper (n : ℕ) (hn : Even n) (h : 4 * 10 ^ 32 < n) :
    AtMostPrimes 6 n :=
  large_even_of_count count_lower n hn (by simp only [n₀]; omega)

end LeanLab.Ramare1995.Decomp369b
