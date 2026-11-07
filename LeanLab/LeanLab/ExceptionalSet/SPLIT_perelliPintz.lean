/-
Split of the sealed theorem `perelliPintz : Theorem5` of `LeanLab.ExceptionalSet.Pintz2021`,
the bound `E_2(N) ≪_ε N^{4/5+ε}` for the number of `n ≤ N` whose `2 n²` is not a sum of two
primes. The target states exactly `: Theorem5`, that is
`∀ ε > 0, ∃ C, ∀ N ≥ 1, EPoly 2 N ≤ C * N ^ (4 / 5 + ε)`.

The cut is by the two parity classes inside dyadic blocks. The block `2 ^ j < n ≤ 2 ^ (j + 1)`
is split into its even and its odd `n`, each class getting its own count bound at the scale
`2 ^ (j * (4 / 5 + ε))`; the assembly `perelliPintz_split` adds the two class counts back to the
block, the blocks by an induction on `j`, and passes from a power of two to an arbitrary `N` by
monotonicity of `EPoly 2`. It proves the target's statement verbatim from the two leaves and does
not use the unsplit theorem.

Why the parity split is the right joint here: `2 n²` is `2 mod 8` for odd `n` and `0 mod 8` for
even `n`, and a sum of two odd primes is `2, 4, 6` or `0 mod 8` according as the two primes are
`1, 3, 5, 7 mod 8`; the local densities, hence the main term the count is compared with, differ
between the two classes, so a proof of the block estimate has to run the two classes separately
anyway. Neither leaf alone gives the target: each counts one class only.

Both classes are inhabited in every block beyond the first, and the block `(1, 2]` is even, so no
hypothesis here is unsatisfiable. Tested at the degenerate scales: `j = 0` gives block `{2}`,
`2 * 2 ^ 2 = 8 = 3 + 5` is a Goldbach sum, both leaves read `0 ≤ C` there; the odd class is empty
at `j = 0`; the two classes are taken as `Even` and `Odd`, not as `2 ∣ ·` and its negation, so
`n = 0` never enters (the block starts at `1`).

Strength: the two leaves together are the block estimate at every scale, so with the assembly this
cut is a scope split of one asymptotic estimate rather than a reduction of its difficulty. What it
buys is a work list whose pieces differ in local density, and a bookkeeping (summation over a
block, induction over dyadic scales, monotone transfer from `2 ^ j` to `N`) that is already proved
here and needs no re-derivation when the leaves are closed.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.Pintz2021

namespace LeanLab.ExceptionalSet.Pintz2021

open Real Filter Topology LeanLab.ExceptionalSet

attribute [local instance] Classical.propDecidable

/-! ### The two leaves -/

/-- LEAF. Step 1 of the split: the even `n` of the dyadic block `2 ^ j < n ≤ 2 ^ (j + 1)` whose
`2 n ^ 2` is not a sum of two primes are, at that scale, as few as the target exponent allows.
This is the whole analytic content of the theorem restricted to the class `2 mod 8` of `2 n ^ 2`,
so it is strictly weaker than the target, which also counts the odd class. -/
theorem leaf_block_even (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      (((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
          (fun n => Even n ∧ ¬ IsGoldbachSum (2 * n ^ 2))).card : ℝ)
        ≤ C * ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε)) := by
  sorry

/-- LEAF. Step 2 of the split: the same count for the odd `n` of the dyadic block
`2 ^ j < n ≤ 2 ^ (j + 1)`, that is for the class `2 mod 8` of `2 n ^ 2`, where the local density
of the representations differs from the even class of step 1. Again one class only, so strictly
weaker than the target. -/
theorem leaf_block_odd (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      (((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
          (fun n => Odd n ∧ ¬ IsGoldbachSum (2 * n ^ 2))).card : ℝ)
        ≤ C * ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε)) := by
  sorry

/-! ### Bookkeeping, no sorry -/

/-- `EPoly 2` is monotone in the bound. -/
private theorem EPoly_two_mono {N M : ℕ} (h : N ≤ M) : EPoly 2 N ≤ EPoly 2 M := by
  unfold EPoly
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hIN, hg⟩ := Finset.mem_filter.mp hn
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIN
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, le_trans h2 h⟩, hg⟩

/-- At the first scale only `n = 1`, and `2` is not a sum of two primes. -/
private theorem EPoly_two_one : EPoly 2 1 = 1 := by
  unfold EPoly
  have h : (Finset.Icc 1 1).filter (fun n => ¬ IsGoldbachSum (2 * n ^ 2)) = {1} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hg⟩
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, by simpa using not_goldbach_two⟩
  rw [h]
  simp

/-- The dyadic block: `EPoly 2` at the upper end is the value at the lower end plus the count in
the block `2 ^ j < n ≤ 2 ^ (j + 1)`. -/
private theorem EPoly_two_block (j : ℕ) :
    EPoly 2 (2 ^ (j + 1)) ≤ EPoly 2 (2 ^ j) +
      ((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
        (fun n => ¬ IsGoldbachSum (2 * n ^ 2))).card := by
  unfold EPoly
  have hIcc : Finset.Icc 1 (2 ^ (j + 1)) =
      Finset.Icc 1 (2 ^ j) ∪ Finset.Icc (2 ^ j + 1) (2 ^ (j + 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hn : n ≤ 2 ^ j
      · exact Or.inl ⟨h1, hn⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j))⟩
      · exact ⟨by omega, h2⟩
  rw [hIcc, Finset.filter_union]
  exact Finset.card_union_le _ _

/-- Every `n` of the block is even or odd, so the block count is at most the sum of the two class
counts. -/
private theorem block_le_parity (j : ℕ) :
    ((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
        (fun n => ¬ IsGoldbachSum (2 * n ^ 2))).card
      ≤ ((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
            (fun n => Even n ∧ ¬ IsGoldbachSum (2 * n ^ 2))).card
        + ((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
            (fun n => Odd n ∧ ¬ IsGoldbachSum (2 * n ^ 2))).card := by
  have hsub : (Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
        (fun n => ¬ IsGoldbachSum (2 * n ^ 2))
      ⊆ (Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
            (fun n => Even n ∧ ¬ IsGoldbachSum (2 * n ^ 2))
        ∪ (Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
            (fun n => Odd n ∧ ¬ IsGoldbachSum (2 * n ^ 2)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_union] at hn ⊢
    rcases Nat.even_or_odd n with he | ho
    · exact Or.inl ⟨hn.1, he, hn.2⟩
    · exact Or.inr ⟨hn.1, ho, hn.2⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The two leaves give one constant for the whole count at every dyadic scale, by induction on
the scale; the geometric growth of `2 ^ (j * (4 / 5 + ε))` is what makes the increments summable
under a single constant. -/
private theorem dyadic_two_pow_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j : ℕ,
      (EPoly 2 (2 ^ j) : ℝ) ≤ K * ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := leaf_block_even ε hε
  obtain ⟨C₂, hC₂, h₂⟩ := leaf_block_odd ε hε
  have hθ : 0 < 4 / 5 + ε := by linarith
  have ht : (1 : ℝ) < (2 : ℝ) ^ (4 / 5 + ε) := Real.one_lt_rpow (by norm_num) hθ
  have hden : 0 < (2 : ℝ) ^ (4 / 5 + ε) - 1 := by linarith
  have hC : 0 ≤ C₁ + C₂ := by linarith
  set K : ℝ := (C₁ + C₂) / ((2 : ℝ) ^ (4 / 5 + ε) - 1) + 1 with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have : 0 ≤ (C₁ + C₂) / ((2 : ℝ) ^ (4 / 5 + ε) - 1) := div_nonneg hC hden.le
    linarith
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 ≤ (C₁ + C₂) / ((2 : ℝ) ^ (4 / 5 + ε) - 1) := div_nonneg hC hden.le
    linarith
  have hKC : K + (C₁ + C₂) ≤ K * (2 : ℝ) ^ (4 / 5 + ε) := by
    have hd : (2 : ℝ) ^ (4 / 5 + ε) - 1 ≠ 0 := ne_of_gt hden
    have hmul : ((C₁ + C₂) / ((2 : ℝ) ^ (4 / 5 + ε) - 1) + 1)
        * ((2 : ℝ) ^ (4 / 5 + ε) - 1) = (C₁ + C₂) + ((2 : ℝ) ^ (4 / 5 + ε) - 1) := by
      rw [add_mul, one_mul, div_mul_cancel₀ (C₁ + C₂) hd]
    rw [hK]
    nlinarith [hmul, hden]
  refine ⟨K, hK0, fun j => ?_⟩
  induction j with
  | zero =>
    have h0 : (EPoly 2 (2 ^ 0) : ℝ) = 1 := by
      have h : EPoly 2 (2 ^ 0) = 1 := by simpa using EPoly_two_one
      rw [h]
      norm_num
    have h1 : ((((2 : ℕ) ^ 0 : ℕ) : ℝ) ^ (4 / 5 + ε)) = 1 := by
      rw [show ((((2 : ℕ) ^ 0 : ℕ)) : ℝ) = 1 by norm_num, Real.one_rpow]
    rw [h0, h1, mul_one]
    exact hK1
  | succ j ih =>
    have hstep : (EPoly 2 (2 ^ (j + 1)) : ℝ) ≤
        (EPoly 2 (2 ^ j) : ℝ) + (C₁ + C₂) * ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε)) := by
      have hb : (EPoly 2 (2 ^ (j + 1)) : ℝ) ≤ (EPoly 2 (2 ^ j) : ℝ) +
          ((((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
            (fun n => ¬ IsGoldbachSum (2 * n ^ 2))).card : ℕ) : ℝ) := by
        exact_mod_cast EPoly_two_block j
      have hpar : ((((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
            (fun n => ¬ IsGoldbachSum (2 * n ^ 2))).card : ℕ) : ℝ)
          ≤ ((((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
              (fun n => Even n ∧ ¬ IsGoldbachSum (2 * n ^ 2))).card : ℕ) : ℝ)
            + ((((Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter
              (fun n => Odd n ∧ ¬ IsGoldbachSum (2 * n ^ 2))).card : ℕ) : ℝ) := by
        exact_mod_cast block_le_parity j
      have he := h₁ j
      have ho := h₂ j
      linarith
    have hpow : ((((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) ^ (4 / 5 + ε))
        = (2 : ℝ) ^ (4 / 5 + ε) * ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε)) := by
      have hc : ((((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)) = 2 * ((((2 : ℕ) ^ j : ℕ) : ℝ)) := by
        rw [pow_succ]
        push_cast
        ring
      rw [hc, Real.mul_rpow (by norm_num) (by positivity)]
    have hX : (0 : ℝ) ≤ ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε)) :=
      Real.rpow_nonneg (by positivity) _
    rw [hpow]
    have h1 : K + (C₁ + C₂) ≤ K * (2 : ℝ) ^ (4 / 5 + ε) := hKC
    have h2 : (EPoly 2 (2 ^ j) : ℝ) ≤
        K * ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε)) := ih
    have h3 : (K + (C₁ + C₂)) * ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε))
        ≤ (K * (2 : ℝ) ^ (4 / 5 + ε)) * ((((2 : ℕ) ^ j : ℕ) : ℝ) ^ (4 / 5 + ε)) :=
      mul_le_mul_of_nonneg_right h1 hX
    nlinarith [hstep, h2, h3]

/-- The target's statement, `: Theorem5`, from the two leaves. -/
theorem perelliPintz_split : Theorem5 := by
  intro ε hε
  obtain ⟨K, hK0, hKb⟩ := dyadic_two_pow_bound ε hε
  refine ⟨K * (2 : ℝ) ^ (4 / 5 + ε), fun N hN => ?_⟩
  have hθ : 0 < 4 / 5 + ε := by linarith
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set J : ℕ := Nat.log 2 N + 1 with hJ
  have hJ1 : N ≤ 2 ^ J := by
    rw [hJ]
    exact le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) N)
  have hJ2 : 2 ^ J ≤ 2 * N := by
    rw [hJ]
    have hN0 : N ≠ 0 := by omega
    calc 2 ^ (Nat.log 2 N + 1) = 2 * 2 ^ (Nat.log 2 N) := by rw [pow_succ]; ring
      _ ≤ 2 * N := by
          have hlog := Nat.pow_log_le_self 2 hN0
          omega
  have hmono : (EPoly 2 N : ℝ) ≤ (EPoly 2 (2 ^ J) : ℝ) := by
    exact_mod_cast EPoly_two_mono hJ1
  have hscale : ((((2 : ℕ) ^ J : ℕ) : ℝ) ^ (4 / 5 + ε)) ≤ (2 * (N : ℝ)) ^ (4 / 5 + ε) := by
    apply Real.rpow_le_rpow (by positivity) _ hθ.le
    exact_mod_cast hJ2
  calc (EPoly 2 N : ℝ) ≤ (EPoly 2 (2 ^ J) : ℝ) := hmono
    _ ≤ K * ((((2 : ℕ) ^ J : ℕ) : ℝ) ^ (4 / 5 + ε)) := hKb J
    _ ≤ K * (2 * (N : ℝ)) ^ (4 / 5 + ε) := by
        exact mul_le_mul_of_nonneg_left hscale hK0
    _ = K * (2 : ℝ) ^ (4 / 5 + ε) * (N : ℝ) ^ (4 / 5 + ε) := by
        rw [Real.mul_rpow (by norm_num) hNpos.le]
        ring

#print axioms perelliPintz_split
