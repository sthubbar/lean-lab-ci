import LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-!
Split of `leaf_coprime_selected` of `LeanLab.ExceptionalSet.UpJ200.Decomp559b`.

The statement being split asks, for `1 < γ < 3/2` and `a > 0`, for a positive cap on the
truncation parameter, a positive cap on the height parameter, positive constants `c` and `A`
and a threshold `N₀`, such that for every admissible truncation, every `N ≥ N₀`, every
conductor `r` selected by `SelectedRealZero`, every index `n` of the floor window and every
shift `j` in `{0, 1}` for which the adjacent integer `ν_n + j` is even and at most `F γ N`,
provided `r ≠ 1` and `ν_n + j` is coprime to `r`, the real part of the major arc integral at
that even integer is at least `c F γ N` minus `A F γ N` times the divisor error.

The split has three parts. The parity condition `Even (ν_n + j)` with `j` in `{0, 1}` forces
`j = 0` when `ν_n` is even and `j = 1` when `ν_n` is odd, so the even adjacent integer is
`ν_n` in the first case and `ν_n + 1` in the second; the first two leaves are the two halves
of that dichotomy, each naming one even frequency only and dropping the shift parameter and
the parity condition on it. The third leaf is that the divisor envelope is nonnegative, so
adding `A F γ N` times it can only raise the right hand side.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Even frequency half of the parity dichotomy, coprime conductor. On an index of the
floor window whose floor value `ν_n` is even, the even adjacent integer is `ν_n` itself, and
for a selected conductor other than one with `ν_n` coprime to it the real part of the major
arc integral at that single frequency already dominates `c F γ N`. One frequency, no shift
parameter, no parity condition on a shift, and no additive divisor error. -/
theorem leaf_coprime_F1253_even (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n) r = 1 →
                c * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re := by
  sorry

/-- LEAF. Odd frequency half of the parity dichotomy, coprime conductor. On an index of the
floor window whose floor value `ν_n` is odd, the even adjacent integer is the upper neighbour
`ν_n + 1`, and for a selected conductor other than one with `ν_n + 1` coprime to it the real
part of the major arc integral at that single frequency already dominates `c F γ N`. One
frequency, no shift parameter, no parity condition on a shift, and no additive divisor
error. -/
theorem leaf_coprime_F1253_odd (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n + 1) r = 1 →
                c * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re := by
  sorry

/-- LEAF. The divisor envelope of the split statement is nonnegative, so the additive error
term it contributes can only raise the right hand side. The claim is made for every conductor,
every truncation value and every frequency, including the degenerate ones: a nonpositive
truncation value empties the finite range and gives the zero contribution, and every summand
is a quotient of naturals divided by positive totients. -/
theorem leaf_coprime_F1253_divisor_nonneg (r : ℕ) (P : ℝ) (m : ℤ) :
    0 ≤ divisorError r P m := by
  have hsum : 0 ≤ ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
      (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) :=
    Finset.sum_nonneg (fun q _ => by positivity)
  have htsum : 0 ≤ ∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0 :=
    tsum_nonneg (fun q => by split_ifs <;> positivity)
  unfold divisorError
  rcases lt_or_ge 0 P with hP | hP
  · exact add_nonneg (mul_nonneg (div_nonneg (by positivity) hP.le) hsum)
      (mul_nonneg (by positivity) htsum)
  · have hzero : ⌊P⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have hempty : (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q) = ∅ := by
      rw [hzero]
      have hI : (Icc 1 (0 : ℕ)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        simp only [Finset.mem_Icc] at hq
        omega
      rw [hI, Finset.filter_empty]
    rw [hempty, Finset.sum_empty, mul_zero, zero_add]
    exact mul_nonneg (by positivity) htsum

/-- Assembly of `leaf_coprime_selected`: the two frequency halves supply the lower bound at
whichever even adjacent integer the parity condition selects, and the nonnegativity of the
divisor envelope supplies the additive error term. -/
theorem leaf_coprime_selected_F1253 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r ≠ 1 → Int.gcd (nu γ n + j) r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨δe, hδe, he⟩ := leaf_coprime_F1253_even γ h1 h2 a ha
  obtain ⟨δo, hδo, ho⟩ := leaf_coprime_F1253_odd γ h1 h2 a ha
  refine ⟨min δe δo, lt_min hδe hδo, ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hδe', hδo'⟩ := lt_min_iff.mp hδsmall
  obtain ⟨κe, hκe, he⟩ := he δ hδ hδe'
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ hδo'
  refine ⟨min κe κo, lt_min hκe hκo, ?_⟩
  intro κ hκ hκsmall
  obtain ⟨hκe', hκo'⟩ := le_min_iff.mp hκsmall
  obtain ⟨ce, hce, Ne, he⟩ := he κ hκ hκe'
  obtain ⟨co, hco, No, ho⟩ := ho κ hκ hκo'
  refine ⟨min ce co, 1, lt_min hce hco, one_pos, max Ne No, ?_⟩
  intro N hN
  obtain ⟨hNe, hNo⟩ := max_le_iff.mp hN
  intro r hr hrP hs j hj n hn heven hm hr1 hgcd
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  by_cases hν : Even (nu γ n)
  · have hj0 : j = 0 := by
      rcases hj with h | h
      · exact h
      · exfalso
        subst h
        obtain ⟨k, hk⟩ := heven
        obtain ⟨l, hl⟩ := hν
        omega
    subst hj0
    have hmain : ce * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re :=
      he N hNe r hr hrP hs n hn hν (by simpa using hm) hr1 (by simpa using hgcd)
    have hlow : (min ce co) * F γ N ≤ ce * F γ N :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hX
    have hslack : (0 : ℝ) ≤ (1 : ℝ) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) :=
      mul_nonneg (mul_nonneg zero_le_one hX) (leaf_coprime_F1253_divisor_nonneg r _ _)
    have hgoal : (min ce co) * F γ N ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
          (1 : ℝ) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
      linarith only [hmain, hlow, hslack]
    simpa using hgoal
  · have hj1 : j = 1 := by
      rcases hj with h | h
      · exfalso
        subst h
        exact hν (by simpa using heven)
      · exact h
    subst hj1
    have hmain : co * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re :=
      ho N hNo r hr hrP hs n hn hν (by simpa using hm) hr1 (by simpa using hgcd)
    have hlow : (min ce co) * F γ N ≤ co * F γ N :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hX
    have hslack : (0 : ℝ) ≤
        (1 : ℝ) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) :=
      mul_nonneg (mul_nonneg zero_le_one hX) (leaf_coprime_F1253_divisor_nonneg r _ _)
    have hgoal : (min ce co) * F γ N ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
          (1 : ℝ) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
      linarith only [hmain, hlow, hslack]
    simpa using hgoal

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
